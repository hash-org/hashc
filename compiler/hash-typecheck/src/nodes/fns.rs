use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::Context,
    tir::{FnDefId, FnTy, NodeOrigin, Ty, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::{CheckResult, CheckState},
        normalisation::{already_normalised, NormaliseResult},
        unification::UnifyResult,
        Operations,
    },
};

impl<E: TcEnv> Operations<FnTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _: &mut Context,
        fn_ty: &mut FnTy,
        item_ty: Self::TyNode,
        _: Self::Node,
    ) -> CheckResult {
        let state = CheckState::new();
        state.then(self.check_is_universe(item_ty))?;
        self.infer_ops().infer_params(fn_ty.params, || {
            self.infer_ops().infer_term(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
        })?;
        state.done()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut FnTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        already_normalised()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        f1: &mut FnTy,
        f2: &mut FnTy,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> UnifyResult {
        if !self.uni_ops().fn_modalities_match(*f1, *f2) {
            self.uni_ops().mismatching_atoms(src_id, target_id)?;
            Ok(())
        } else {
            // Unify parameters and apply to return types
            self.uni_ops().unify_params(f1.params, f2.params, || {
                self.uni_ops().unify_terms(f1.return_ty, f2.return_ty)
            })?;

            let forward_sub = self.sub_ops().create_sub_from_param_names(f1.params, f2.params);
            f2.return_ty = self.sub_ops().apply_sub(f2.return_ty, &forward_sub);

            let backward_sub = self.sub_ops().create_sub_from_param_names(f2.params, f1.params);
            f1.return_ty = self.sub_ops().apply_sub(f1.return_ty, &backward_sub);

            src_id.set(src_id.value().with_data((*f1).into()));
            target_id.set(target_id.value().with_data((*f2).into()));

            Ok(())
        }
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut FnTy) {
        todo!()
    }
}

impl<E: TcEnv> Operations<FnDefId> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = FnDefId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut FnDefId,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut FnDefId,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _src: &mut FnDefId,
        _target: &mut FnDefId,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut FnDefId) {
        todo!()
    }
}
