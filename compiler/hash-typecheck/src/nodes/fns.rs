use hash_tir::{
    context::Context,
    tir::{FnDefId, FnTy, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult, normalisation::NormaliseResult, unification::UnifyResult, Operations,
    },
};

impl<E: TcEnv> Operations<FnTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut FnTy,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut FnTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _src: &mut FnTy,
        _target: &mut FnTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
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
