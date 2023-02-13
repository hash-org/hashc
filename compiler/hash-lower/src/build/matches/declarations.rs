//! This deals with lowering declarations,assigning them to a [Local],
//! and later resolving references to the locals with the current [Builder].

use hash_ast::ast;
use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::Identifier, location::Span};
use hash_tir::scopes::DeclTerm; begin migrating builder to using TIR
use hash_utils::store::Store;

use super::{candidate::Candidate, BlockAnd, Builder};
use crate::build::{place::PlaceBuilder, unpack, BlockAndExtend, LocalKey};

impl<'tcx> Builder<'tcx> {
    /// Push a [LocalDecl] in the current [Builder] with the associated
    /// [LocalKey]. This will put the [LocalDecl] into the declarations, and
    /// create an entry in the lookup map so that the [Local] can be looked up
    /// via the name of the local and the scope that it is in.
    pub(crate) fn push_local(&mut self, decl: LocalDecl, key: LocalKey) -> Local {
        let index = self.declarations.push(decl);

        // If the declaration has a name i.e. not an auxiliary local, then
        // we can push it into the `declaration_map`.
        if decl.name.is_some() {
            self.declaration_map.insert(key, index);
        }

        index
    }

    /// This function handles the lowering of an declaration term.
    pub(crate) fn lower_declaration(
        &mut self,
        mut block: BasicBlock,
        decl: &'tcx DeclTerm,
        decl_span: Span,
    ) -> BlockAnd<()> {
        if let Some(value) = &decl.value {
            // First, we declare all of the bindings that are present
            // in the pattern, and then we place the expression into
            // the pattern using `expr_into_pat`.
            self.declare_bindings(decl.pat.ast_ref());

            unpack!(block = self.tir_term_into_pat(block, decl.bind_pat, value));
        } else {
            panic_on_span!(
                decl_span.into_location(self.source_id),
                self.source_map(),
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
    fn declare_bindings(&mut self, pat: ast::AstNodeRef<'tcx, ast::Pat>) {
        self.visit_primary_pattern_bindings(pat, &mut |this, mutability, name, _span, ty| {
            let local = LocalDecl::new(name, mutability, ty);
            let scope = this.current_scope();

            this.push_local(local, scope);
        })
    }

    fn visit_primary_pattern_bindings(
        &mut self,
        pat: ast::AstNodeRef<'tcx, ast::Pat>,
        f: &mut impl FnMut(&mut Self, Mutability, Identifier, Span, IrTyId),
    ) {
        match &pat.body {
            ast::Pat::Binding(ast::BindingPat { name, mutability, .. }) => {
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
            ast::Pat::Constructor(ast::ConstructorPat { fields, spread, .. })
            | ast::Pat::Tuple(ast::TuplePat { fields, spread }) => {
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
            ast::Pat::Array(ast::ArrayPat { fields, spread }) => {
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
            ast::Pat::Or(ast::OrPat { ref variants }) => {
                // We only need to visit the first variant since we already
                // check that the variant bindings are all the same.
                if let Some(pat) = variants.get(0) {
                    self.visit_primary_pattern_bindings(pat.ast_ref(), f);
                }
            }
            ast::Pat::If(ast::IfPat { pat, .. }) => {
                self.visit_primary_pattern_bindings(pat.ast_ref(), f);
            }
            // These patterns never have any bindings.
            ast::Pat::Module(_)
            | ast::Pat::Range(_)
            | ast::Pat::Access(_)
            | ast::Pat::Lit(_)
            | ast::Pat::Wild(_) => {}
        }
    }

    /// Lower a given [ast::Expr] into the provided [ast::Pat]. It is expected
    /// that the pattern is irrefutable, since this is verified during
    /// typechecking via exhaustiveness.
    fn tir_term_into_pat(
        &mut self,
        mut block: BasicBlock,
        pat: ast::AstNodeRef<'tcx, ast::Pat>,
        expr: ast::AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<()> {
        match &pat.body {
            ast::Pat::Binding(ast::BindingPat { name, .. }) => {
                // we lookup the local from the current scope, and get the place of where
                // to place this value.
                let local = self.lookup_local(name.ident).unwrap();
                let place = Place::from_local(local, self.ctx);

                unpack!(block = self.term_into_dest(place, block, expr));
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

    /// Construct a [Candidate] for a given [ast::Pat], and then lower
    /// the pattern with a single candidate, and the expression that
    /// is the initialising value of the patterns.
    fn place_into_pat(
        &mut self,
        block: BasicBlock,
        pat: ast::AstNodeRef<'tcx, ast::Pat>,
        place: PlaceBuilder,
    ) -> BlockAnd<()> {
        let pat_id = self.pat_id_of_node(pat.id());
        let pat_span = pat.span();

        let mut candidate = Candidate::new(pat_span, pat_id, &place, false);
        self.lower_match_tree(block, pat_span, pat_span, &mut [&mut candidate]);

        self.bind_pat(pat_span, pat, candidate).unit()
    }
}
