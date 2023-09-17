use hash_tir::{
    context::Context,
    tir::{ArgsId, ParamsId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult, normalisation::NormaliseResult, unification::UnifyResult, Operations,
    },
};

impl<E: TcEnv> Operations<ArgsId> for Checker<'_, E> {
    type TyNode = ParamsId;
    type Node = ArgsId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut ArgsId,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut ArgsId,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _src: &mut ArgsId,
        _target: &mut ArgsId,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ArgsId) {
        todo!()
    }
}
