use hash_tir::{context::Context, tir::ParamsId};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult, normalisation::NormaliseResult, unification::UnifyResult, Operations,
    },
};

impl<E: TcEnv> Operations<ParamsId> for Checker<'_, E> {
    type Node = ParamsId;
    type TyNode = ();

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut ParamsId,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut ParamsId,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _src: &mut ParamsId,
        _target: &mut ParamsId,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ParamsId) {
        todo!()
    }
}
