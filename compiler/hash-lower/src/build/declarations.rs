use hash_ast::ast::{self, AstNodeRef, Declaration};
use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_reporting::macros::panic_on_span;
use hash_source::identifier::Identifier;
use hash_types::{
    pats::{BindingPat, Pat},
    scope::{Member, ScopeId, ScopeKind},
};
use hash_utils::store::Store;

use super::{BlockAnd, Builder};
use crate::build::{unpack, BlockAndExtend};

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
    ) -> BlockAnd<()> {
        if self.dead_ends.contains(&decl.pat.id()) {
            return block.unit();
        }

        // Declare all locals that need to be declared based on the
        // pattern.
        self.visit_bindings(decl.pat.ast_ref());

        if let Some(value) = &decl.value {
            unpack!(block = self.expr_into_pat(block, decl.pat.ast_ref(), value.ast_ref()));
        } else {
            panic_on_span!(
                decl.pat.span().into_location(self.source_id),
                self.source_map,
                "expected initialisation value, declaration are expected to have values (for now)."
            );
        }

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }

    /// Visit all of the bindings that are declared in the current pattern, and
    /// add them to the current builder declarations.
    pub(crate) fn visit_bindings(&mut self, pat: AstNodeRef<'tcx, ast::Pat>) {
        let node_id = pat.id();

        match pat.body {
            ast::Pat::Binding(ast::BindingPat { name: _, visibility: _, mutability: _ }) => {
                // resolve the type of this binding
                let (name, mutability) =
                    self.tcx.pat_store.map_fast(self.pat_id_of_node(node_id), |pat| {
                        let Pat::Binding(BindingPat { mutability, name, .. }) = pat else {
                            unreachable!("expected binding pattern");
                        };

                        (*name, (*mutability).into())
                    });

                let ty = self.ty_id_of_node(node_id);
                self.declare_binding(name, ty, mutability)
            }
            ast::Pat::Tuple(ast::TuplePat { fields }) => {
                // @@Todo: deal with associating a projection here.

                for tuple_entry in fields.iter() {
                    let ast::TuplePatEntry { pat, .. } = tuple_entry.body();
                    self.visit_bindings(pat.ast_ref());
                }
            }
            ast::Pat::Constructor(_) => unimplemented!(),
            ast::Pat::List(_) => unimplemented!(),
            ast::Pat::Or(_) => unimplemented!(),
            ast::Pat::If(_) => unimplemented!(),
            ast::Pat::Lit(_)
            | ast::Pat::Module(_)
            | ast::Pat::Access(_)
            | ast::Pat::Range(_)
            | ast::Pat::Wild(_)
            | ast::Pat::Spread(_) => {}
        }
    }

    /// Declare a [Local] with the given metadata in the current builder.
    fn declare_binding(&mut self, name: Identifier, ty: IrTyId, mutability: Mutability) {
        let local = LocalDecl::new(name, mutability, ty);
        let scope_id = self.scope_stack.last().unwrap();

        self.push_local(local, *scope_id);
    }

    /// Put the right-hand side expression into the provided irrefutable
    /// pattern.
    fn expr_into_pat(
        &mut self,
        mut block: BasicBlock,
        irrefutable_pat: AstNodeRef<'tcx, ast::Pat>,
        rvalue: AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<()> {
        match irrefutable_pat.body {
            // The simple case of a just writing into the binding, we can
            // directly assign into the binding that is provided.
            ast::Pat::Binding(ast::BindingPat { name, .. }) => {
                let place = Place::from_local(self.lookup_local(name.ident).unwrap(), self.storage);
                unpack!(block = self.expr_into_dest(place, block, rvalue));
                block.unit()
            }
            ast::Pat::Wild(_) => unimplemented!(),
            ast::Pat::Constructor(_) => unimplemented!(),
            ast::Pat::Tuple(_) => unimplemented!(),
            ast::Pat::List(_) => unimplemented!(),
            ast::Pat::Lit(_) => unimplemented!(),
            ast::Pat::Or(_) => unimplemented!(),
            pat => {
                panic!("reached irrefutable pattern: {pat:?} in `expr_into_pat`");
            }
        }
    }
}
