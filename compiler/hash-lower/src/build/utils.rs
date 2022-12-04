//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ast::ast::{AstNodeId, AstNodeRef};
use hash_ir::{
    ir::{AssertKind, BasicBlock, LocalDecl, Place, TerminatorKind},
    ty::{AdtData, AdtId, IrTy, IrTyId, Mutability},
};
use hash_source::location::Span;
use hash_types::pats::PatId;
use hash_utils::store::Store;

use super::{
    ty::{convert_term_into_ir_ty, lower_term},
    Builder,
};

impl<'tcx> Builder<'tcx> {
    /// Function to get the associated [TermId] with the
    /// provided [AstNodeId].
    #[inline]
    pub(crate) fn ty_id_of_node(&self, id: AstNodeId) -> IrTyId {
        let term_id = self.tcx.node_info_store.node_info(id).map(|f| f.term_id()).unwrap();

        // We need to try and look up the type within the cache, if not
        // present then we create the type by converting the term into
        // the type.

        convert_term_into_ir_ty(term_id, self.tcx, self.storage)
    }

    /// Function to get the associated [IrTy] with the
    /// provided [AstNodeId]. This does not attempt to cache the
    /// type.
    #[inline]
    pub(crate) fn ty_of_node(&self, id: AstNodeId) -> IrTy {
        let term_id = self.tcx.node_info_store.node_info(id).map(|f| f.term_id()).unwrap();

        // We need to try and look up the type within the cache, if not
        // present then we create the type by converting the term into
        // the type.

        lower_term(term_id, self.tcx, self.storage)
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

    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.tcx.location_store.get_span(id).unwrap()
    }

    /// Apply a function on a [IrTy::Adt].
    pub(crate) fn map_on_adt<T>(&self, ty: IrTyId, f: impl FnOnce(&AdtData, AdtId) -> T) -> T {
        self.storage.ty_store().map_fast(ty, |ty| {
            self.storage.adt_store().map_fast(ty.as_adt(), |adt| f(adt, ty.as_adt()))
        })
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => tmp.clone(),
            None => {
                let ty = IrTy::unit(self.storage);
                let ty_id = self.storage.ty_store().create(ty);

                let local = LocalDecl::new_auxiliary(ty_id, Mutability::Immutable);
                let local_id = self.declarations.push(local);

                let place = Place::from(local_id);
                self.tmp_place = Some(place.clone());

                place
            }
        }
    }

    /// Create an assertion on a particular block
    pub(crate) fn assert(
        &mut self,
        block: BasicBlock,
        condition: Place,
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
}
