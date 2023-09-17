use hash_tir::{
    context::Context,
    tir::{AccessTerm, ArgsId, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult, normalisation::NormaliseResult, unification::UnifyResult, Operations,
    },
};

impl<E: TcEnv> Operations<AccessTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = ArgsId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut AccessTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut AccessTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _src: &mut AccessTerm,
        _target: &mut AccessTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut AccessTerm) {
        todo!()
    }
}
