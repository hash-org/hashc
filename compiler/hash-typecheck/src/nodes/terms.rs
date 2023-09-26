use hash_tir::{
    context::Context,
    tir::{TermId, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult,
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::{UnificationOptions, UnifyResult},
        Operations,
    },
};

impl<E: TcEnv> Operations<TermId> for Checker<'_, E> {
    type Node = TermId;
    type TyNode = TyId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut TermId,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: &mut TermId,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut TermId,
        _target: &mut TermId,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TermId) {
        todo!()
    }
}
