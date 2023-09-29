use hash_tir::{
    context::Context,
    tir::{LitId, TyId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        OperationsOnNode,
    },
};

impl<E: TcEnv> OperationsOnNode<LitId> for Tc<'_, E> {
    type TyNode = TyId;

    fn check_node(&self, _ctx: &mut Context, _item: LitId, _item_ty: Self::TyNode) -> TcResult<()> {
        todo!()
    }

    fn normalise_node(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: LitId,
    ) -> NormaliseResult<LitId> {
        todo!()
    }

    fn unify_nodes(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: LitId,
        _target: LitId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: LitId) {
        todo!()
    }
}
