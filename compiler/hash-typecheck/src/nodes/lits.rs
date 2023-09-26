use hash_tir::{
    context::Context,
    tir::{LitId, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<LitId> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = LitId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut LitId,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: &mut LitId,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut LitId,
        _target: &mut LitId,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut LitId) {
        todo!()
    }
}
