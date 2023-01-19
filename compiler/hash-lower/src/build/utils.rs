//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [ast::AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ast::ast;
use hash_ir::{
    ir::{AssertKind, BasicBlock, LocalDecl, Operand, Place, TerminatorKind},
    ty::{IrTy, IrTyId, Mutability},
};
use hash_source::location::Span;
use hash_tir::{pats::PatId, terms::TermId};

use super::Builder;

impl<'tcx> Builder<'tcx> {
    /// Function to get the associated [TermId] with the
    /// provided [ast::AstNodeId].
    #[inline]
    pub(crate) fn ty_id_of_node(&self, id: ast::AstNodeId) -> IrTyId {
        // We need to try and look up the type within the cache, if not
        // present then we create the type by converting the term into
        // the type.
        self.lower_term_as_id(self.term_of_node(id))
    }

    /// Function to get the associated [IrTy] with the
    /// provided [ast::AstNodeId]. This does not attempt to cache the
    /// type.
    #[inline]
    pub(crate) fn ty_of_node(&self, id: ast::AstNodeId) -> IrTy {
        self.lower_term(self.term_of_node(id))
    }

    /// Function to get the associated [PatId] with the
    /// provided [ast::AstNodeId].
    #[inline]
    pub(crate) fn pat_id_of_node(&self, id: ast::AstNodeId) -> PatId {
        self.tcx.node_info_store.node_info(id).map(|f| f.pat_id()).unwrap()
    }

    /// Lookup the corresponding [ast::AstNodeId] of [PatId], and then compute
    /// the type associated with this [ast::AstNodeId].
    pub(crate) fn ty_of_pat(&self, id: PatId) -> IrTyId {
        self.tcx.node_info_store.pat_to_node_id(id).map(|id| self.ty_id_of_node(id)).unwrap()
    }

    /// Lookup the corresponding [TermId] of [PatId] and return it.
    pub(crate) fn term_of_pat(&self, id: PatId) -> TermId {
        self.tcx
            .node_info_store
            .pat_to_node_id(id)
            .map(|id| self.tcx.node_info_store.node_info(id).unwrap().term_id())
            .unwrap()
    }

    /// Lookup the corresponding [TermId] of a [ast::AstNodeId] and return it.
    pub(crate) fn term_of_node(&self, id: ast::AstNodeId) -> TermId {
        self.tcx.node_info_store.node_info(id).unwrap().term_id()
    }

    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.tcx.location_store.get_span(id).unwrap()
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => *tmp,
            None => {
                let local =
                    LocalDecl::new_auxiliary(self.ctx.tys().common_tys.unit, Mutability::Immutable);
                let local_id = self.declarations.push(local);

                let place = Place::from_local(local_id, self.ctx);
                self.tmp_place = Some(place);
                place
            }
        }
    }

    /// Create an assertion on a particular block
    pub(crate) fn assert(
        &mut self,
        block: BasicBlock,
        condition: Operand,
        expected: bool,
        kind: AssertKind,
        span: Span,
    ) -> BasicBlock {
        let success_block = self.control_flow_graph.start_new_block();

        self.control_flow_graph.terminate(
            block,
            span,
            TerminatorKind::Assert { condition, expected, kind, target: success_block },
        );

        success_block
    }

    /// Run a lowering operation whilst entering a new scope which is derived
    /// from the provided [ast::AstNodeRef<ast::Expr>].
    ///
    /// N.B. It is assumed that the related expression has an associated scope.
    pub(crate) fn with_scope<T, U>(
        &mut self,
        expr: ast::AstNodeRef<U>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let scope_id = self.tcx.node_info_store.node_info(expr.id()).map(|f| f.scope_id()).unwrap();
        self.scope_stack.push(scope_id);

        let result = f(self);

        let popped = self.scope_stack.pop();
        debug_assert!(popped.is_some() && matches!(popped, Some(id) if id == scope_id));

        result
    }
}
