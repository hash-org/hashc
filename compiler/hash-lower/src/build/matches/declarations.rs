use hash_ast::ast::{
    self, AstNodeRef, BindingPat, ConstructorPat, Declaration, Expr, IfPat, ListPat, OrPat, Pat,
    TuplePat,
};
use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::Identifier, location::Span};
use hash_types::scope::{Member, ScopeId, ScopeKind};
use hash_utils::store::Store;

use super::{candidate::Candidate, BlockAnd, Builder};
use crate::build::{place::PlaceBuilder, unpack, BlockAndExtend};

impl<'tcx> Builder<'tcx> {
    /// Get the current [ScopeId] that is being used within the builder.
    pub(crate) fn current_scope(&self) -> ScopeId {
        *self.scope_stack.last().unwrap()
    }

    /// Push a [LocalDecl] in the current [Builder] with the associated
    /// [ScopeId]. This will put the [LocalDecl] into the declarations, and
    /// create an entry in the lookup map so that the [Local] can be looked up
    /// via the name of the local and the scope that it is in.
    pub(crate) fn push_local(&mut self, decl: LocalDecl, scope: ScopeId) -> Local {
        let decl_name = decl.name;
        let index = self.declarations.push(decl);

        // If the declaration has a name i.e. not an auxiliary local, then
        // we can push it into the `declaration_map`.
        if let Some(name) = decl_name {
            self.declaration_map.insert((scope, name), index);
        }

        index
    }

    /// Get the [Local] associated with the provided [ScopeId] and [Identifier].
    pub(crate) fn lookup_local(&self, name: Identifier) -> Option<Local> {
        self.lookup_item_scope(name)
            .and_then(|(scope_id, _, _)| self.lookup_local_from_scope(scope_id, name))
    }

    /// Lookup a [Local] from a [ScopeId] and a [Identifier].
    pub(crate) fn lookup_local_from_scope(
        &self,
        scope: ScopeId,
        name: Identifier,
    ) -> Option<Local> {
        self.declaration_map.get(&(scope, name)).copied()
    }

    /// Get the [ScopeId] and [Member] of a [Identifier] that is within the
    /// current scope stack.
    pub(crate) fn lookup_item_scope(
        &self,
        name: Identifier,
    ) -> Option<(ScopeId, Member, ScopeKind)> {
        for scope_id in self.scope_stack.iter().rev() {
            // We need to walk up the scopes, and then find the first scope
            // that contains this variable
            match self.tcx.scope_store.map_fast(*scope_id, |scope| (scope.get(name), scope.kind)) {
                // Found in this scope, return the member.
                (Some((member, _)), kind) => return Some((*scope_id, member, kind)),
                // Continue to the next (higher) scope:
                _ => continue,
            }
        }

        None
    }

    /// This function handles the lowering of an expression declaration.
    /// Internally, we check if this declaration needs to be lowered since
    /// this might be declaring a free function within the current function
    /// body, and thus we should not lower it.
    ///
    /// @@Todo: deal with non-trivial dead-ends, i.e. compound patterns that
    /// have dead ends...
    pub(crate) fn lower_declaration(
        &mut self,
        mut block: BasicBlock,
        decl: &'tcx Declaration,
        decl_span: Span,
    ) -> BlockAnd<()> {
        // The dead-ends are provided by discovery and indicate items
        // that the lower should just skip over. As the above @@Todo mentions,
        // this might not entirely work for compound patterns that may have a
        // a single member that is a dead-end, but the rest should be lowered.
        // In this situation, the lowerer will avoid lowering the parts that don't
        // need to be lowered, and later optimised out by the `remove_dead_locals`
        // pass.
        if self.dead_ends.contains(&decl.pat.id()) {
            return block.unit();
        }

        if let Some(value) = &decl.value {
            // First, we declare all of the bindings that are present
            // in the pattern, and then we place the expression into
            // the pattern using `expr_into_pat`.
            self.declare_bindings(decl.pat.ast_ref());

            unpack!(block = self.expr_into_pat(block, decl.pat.ast_ref(), value.ast_ref()));
        } else {
            panic_on_span!(
                decl_span.into_location(self.source_id),
                self.source_map,
                "expected initialisation value, declaration are expected to have values (for now)."
            );
        };

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }

    /// Declare all of the bindings that are present in the left-most variant
    /// of the pattern. This is guaranteed to cover all bindings that can be
    /// bound within the pattern since we have already checked that all pattern
    /// variants declare the same binds of the same type, on the same
    /// pattern level.
    fn declare_bindings(&mut self, pat: AstNodeRef<'tcx, Pat>) {
        self.visit_primary_pattern_bindings(pat, &mut |this, mutability, name, _span, ty| {
            let local = LocalDecl::new(name, mutability, ty);
            let scope = this.current_scope();

            this.push_local(local, scope);
        })
    }

    fn visit_primary_pattern_bindings(
        &mut self,
        pat: AstNodeRef<'tcx, ast::Pat>,
        f: &mut impl FnMut(&mut Self, Mutability, Identifier, Span, IrTyId),
    ) {
        match &pat.body {
            Pat::Binding(BindingPat { name, mutability, .. }) => {
                // @@Todo: when we support `k @ ...` patterns, we need to know
                // when this is a primary pattern or not.
                let ty = self.ty_of_pat(self.pat_id_of_node(pat.id()));

                f(
                    self,
                    mutability
                        .as_ref()
                        .map(|m| (*m.body()).into())
                        .unwrap_or(Mutability::Immutable),
                    name.ident,
                    pat.span(),
                    ty,
                );
            }
            Pat::Constructor(ConstructorPat { fields, spread, .. })
            | Pat::Tuple(TuplePat { fields, spread }) => {
                for field in fields.iter() {
                    self.visit_primary_pattern_bindings(field.pat.ast_ref(), f);
                }

                if let Some(spread_pat) = spread && let Some(name) = &spread_pat.name {
                    f(
                        self,
                        // @@Todo: it should be possible to make this a mutable
                        // pattern reference, for now we assume it is always immutable.
                        Mutability::Immutable,
                        name.ident,
                        pat.span(),
                        self.ty_of_pat(self.pat_id_of_node(pat.id())),
                    )
                }
            }
            Pat::List(ListPat { fields, spread }) => {
                if let Some(spread_pat) = spread && let Some(name) = &spread_pat.name {
                    let index = spread_pat.position;

                    // Create the fields into an iterator, and only take the `prefix`
                    // amount of fields to iterate
                    let prefix_fields = fields.iter().take(index);

                    for field in prefix_fields {
                        self.visit_primary_pattern_bindings(field.ast_ref(), f);
                    }

                    f(
                        self,
                        // @@Todo: it should be possible to make this a mutable
                        // pattern reference, for now we assume it is always immutable.
                        Mutability::Immutable,
                        name.ident,
                        pat.span(),
                        self.ty_of_pat(self.pat_id_of_node(pat.id())),
                    );

                    // Now deal with the suffix fields.
                    let suffix_fields = fields.iter().skip(index);

                    for field in suffix_fields {
                        self.visit_primary_pattern_bindings(field.ast_ref(), f);
                    }
                } else {
                    for field in fields.iter() {
                        self.visit_primary_pattern_bindings(field.ast_ref(), f);
                    }
                }
            }
            Pat::Or(OrPat { ref variants }) => {
                // We only need to visit the first variant since we already
                // check that the variant bindings are all the same.
                if let Some(pat) = variants.get(0) {
                    self.visit_primary_pattern_bindings(pat.ast_ref(), f);
                }
            }
            Pat::If(IfPat { pat, .. }) => {
                self.visit_primary_pattern_bindings(pat.ast_ref(), f);
            }
            // These patterns never have any bindings.
            Pat::Module(_) | Pat::Range(_) | Pat::Access(_) | Pat::Lit(_) | Pat::Wild(_) => {}
        }
    }

    /// Lower a given [Expr] into the provided [Pat]. It is expected that the
    /// pattern is irrefutable, since this is verified during typechecking
    /// via exhaustiveness.
    fn expr_into_pat(
        &mut self,
        mut block: BasicBlock,
        pat: AstNodeRef<'tcx, Pat>,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<()> {
        match &pat.body {
            Pat::Binding(BindingPat { name, .. }) => {
                // we lookup the local from the current scope, and get the place of where
                // to place this value.
                let local = self.lookup_local(name.ident).unwrap();
                let place = Place::from_local(local, self.storage);

                unpack!(block = self.expr_into_dest(place, block, expr));
                block.unit()
            }
            // The long path, we go through creating candidates and then
            // automatically building places for each candidate, etc.
            _ => {
                let place_builder =
                    unpack!(block = self.as_place_builder(block, expr, Mutability::Mutable));
                self.place_into_pat(block, pat, place_builder)
            }
        }
    }

    /// Construct a [Candidate] for a given [Pat], and then lower
    /// the pattern with a single candidate, and the expression that
    /// is the initialising value of the patterns.
    fn place_into_pat(
        &mut self,
        block: BasicBlock,
        pat: AstNodeRef<'tcx, Pat>,
        place: PlaceBuilder,
    ) -> BlockAnd<()> {
        let pat_id = self.pat_id_of_node(pat.id());
        let pat_span = pat.span();

        let mut candidate = Candidate::new(pat_span, pat_id, &place, false);
        self.lower_match_tree(block, pat_span, pat_span, &mut [&mut candidate]);

        self.bind_pat(pat_span, pat, candidate).unit()
    }
}
