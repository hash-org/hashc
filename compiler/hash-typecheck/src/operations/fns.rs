use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, SequenceStoreKey, StoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{HasContext, ScopeKind},
    term_as_variant,
    tir::{FnDefId, FnTy, NodeId, NodeOrigin, ParamsId, Term, TermId, Ty, TyId},
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::{FnInferMode, Tc},
    traits::{OperationsOn, OperationsOnNode, ScopedOperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    /// Create a function type from a list of parameter (type, implicitness) and
    /// a return type.
    ///
    /// If one parameter list is empty, it is skipped.
    pub(crate) fn params_and_ret_to_fn_ty<I: IntoIterator<Item = (ParamsId, bool)>>(
        &self,
        params: I,
        ret: TyId,
    ) -> TyId
    where
        I::IntoIter: DoubleEndedIterator,
    {
        params.into_iter().rev().fold(ret, |acc, (params, implicit)| {
            Ty::from(
                FnTy { params, return_ty: acc, implicit, is_unsafe: false, pure: true },
                acc.origin(),
            )
        })
    }
}

impl<E: TcEnv> OperationsOn<FnTy> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TyId;

    fn check(&self, fn_ty: &mut FnTy, item_ty: Self::AnnotNode, _: Self::Node) -> TcResult<()> {
        self.check_is_universe(item_ty)?;
        self.check_node_scoped(fn_ty.params, (), |()| {
            self.check_node(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
        })?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: FnTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TyId>> {
        already_normalised()
    }

    fn unify(
        &self,
        f1: &mut FnTy,
        f2: &mut FnTy,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> TcResult<()> {
        if !self.fn_modalities_match(*f1, *f2) {
            self.mismatching_atoms(src_id, target_id)?;
            Ok(())
        } else {
            // Unify parameters and apply to return types
            self.unify_nodes_scoped(f1.params, f2.params, |()| {
                self.unify_nodes(f1.return_ty, f2.return_ty)
            })?;
            Ok(())
        }
    }
}

impl<E: TcEnv> Tc<'_, E> {
    /// Whether two function types match in terms of their modality.
    fn fn_modalities_match(&self, f1: FnTy, f2: FnTy) -> bool {
        f1.implicit == f2.implicit && f1.is_unsafe == f2.is_unsafe && f1.pure == f2.pure
    }

    fn check_fn_def_id_annotation(
        &self,
        fn_def_id: FnDefId,
        annotation_ty: TyId,
    ) -> TcResult<FnTy> {
        let fn_def = fn_def_id.value();
        let fn_ty = Ty::from(fn_def.ty, fn_def_id.origin());
        self.check_node(fn_ty, Ty::universe_of(fn_ty))?;
        self.unify_nodes(fn_ty, annotation_ty)?;

        let fn_ty_value = term_as_variant!(self, fn_ty.value(), FnTy);
        fn_def_id.borrow_mut().ty = fn_ty_value;

        Ok(fn_ty_value)
    }
}

impl<E: TcEnv> OperationsOn<FnDefId> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        fn_def_id: &mut FnDefId,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let fn_def_id = *fn_def_id;
        if let Some(fn_ty) = self.try_get_inferred_ty(fn_def_id) {
            let expected =
                Ty::expect_is(original_term_id, Ty::from(fn_ty, fn_def_id.origin().inferred()));
            self.unify_nodes(expected, annotation_ty)?;
            return Ok(());
        }

        self.check_fn_def_id_annotation(fn_def_id, annotation_ty)?;
        let fn_def = fn_def_id.value();

        if self.atom_is_registered(fn_def_id) {
            // Recursive call
            return Ok(());
        }

        self.register_new_atom(fn_def_id, fn_def.ty);

        let fn_def = fn_def_id.value();

        self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
            self.enter_params_scope(fn_def.ty.params, || {
                self.check_node(fn_def.body, fn_def.ty.return_ty)
            })
        })?;

        let fn_ty_id =
            Ty::expect_is(original_term_id, Ty::from(fn_def.ty, fn_def_id.origin().inferred()));
        self.unify_nodes(fn_ty_id, annotation_ty)?;

        self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);

        Ok(())
    }

    fn try_normalise(
        &self,
        _item: FnDefId,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        already_normalised()
    }

    fn unify(
        &self,
        src: &mut FnDefId,
        target: &mut FnDefId,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        self.unification_ok_or_mismatching_atoms(*src == *target, src_node, target_node)
    }
}
