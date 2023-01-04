//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ast::ast::{AstNodeId, AstNodeRef};
use hash_ir::{
    ir::{AssertKind, BasicBlock, LocalDecl, Operand, Place, TerminatorKind},
    ty::{AdtData, AdtId, IrTy, IrTyId, Mutability},
};
use hash_source::location::Span;
use hash_types::{pats::PatId, terms::TermId};
use hash_utils::store::Store;

use super::Builder;

impl<'tcx> Builder<'tcx> {
    /// Function to get the associated [TermId] with the
    /// provided [AstNodeId].
    #[inline]
    pub(crate) fn ty_id_of_node(&self, id: AstNodeId) -> IrTyId {
        // We need to try and look up the type within the cache, if not
        // present then we create the type by converting the term into
        // the type.
        self.convert_term_into_ir_ty(self.term_of_node(id))
    }

    /// Function to get the associated [IrTy] with the
    /// provided [AstNodeId]. This does not attempt to cache the
    /// type.
    #[inline]
    pub(crate) fn ty_of_node(&self, id: AstNodeId) -> IrTy {
        self.lower_term(self.term_of_node(id))
    }

    /// Function to get the associated [PatId] with the
    /// provided [AstNodeId].
    #[inline]
    pub(crate) fn pat_id_of_node(&self, id: AstNodeId) -> PatId {
        self.tcx.node_info_store.node_info(id).map(|f| f.pat_id()).unwrap()
    }

    /// Lookup the corresponding [AstNodeId] of [PatId], and then compute
    /// the type associated with this [AstNodeId].
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

    /// Lookup the corresponding [TermId] of a [AstNodeId] and return it.
    pub(crate) fn term_of_node(&self, id: AstNodeId) -> TermId {
        self.tcx.node_info_store.node_info(id).unwrap().term_id()
    }

    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.tcx.location_store.get_span(id).unwrap()
    }

    /// Apply a function on a [IrTy::Adt].
    pub(crate) fn map_on_adt<T>(&self, ty: IrTyId, f: impl FnOnce(&AdtData, AdtId) -> T) -> T {
        self.storage
            .tys()
            .map_fast(ty, |ty| self.storage.adts().map_fast(ty.as_adt(), |adt| f(adt, ty.as_adt())))
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => *tmp,
            None => {
                let ty = IrTy::unit(self.storage);
                let ty_id = self.storage.tys().create(ty);

                let local = LocalDecl::new_auxiliary(ty_id, Mutability::Immutable);
                let local_id = self.declarations.push(local);

                let place = Place::from_local(local_id, self.storage);
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
    /// from the provided [AstNodeRef<Expr>].
    ///
    /// N.B. It is assumed that the related expression has an associated scope.
    pub(crate) fn with_scope<T, U>(
        &mut self,
        expr: AstNodeRef<U>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let scope_id = self.tcx.node_info_store.node_info(expr.id()).map(|f| f.scope_id()).unwrap();
        self.scope_stack.push(scope_id);

        let result = f(self);

        let popped = self.scope_stack.pop();
        debug_assert!(popped.is_some() && matches!(popped, Some(id) if id == scope_id));

        result
    }

    /// Run some function whilst reading a [IrTy] from a provided [IrTyId].
    ///
    /// N.B. The closure that is passed into this should not attempt to create
    ///      new [IrTy]s, whislt this is checking, this is only meant as a
    /// read-only      context over the whole type storage.
    pub(crate) fn map_ty<T>(&mut self, ty: IrTyId, f: impl FnOnce(&IrTy) -> T) -> T {
        self.storage.tys().map_fast(ty, f)
    }
}
