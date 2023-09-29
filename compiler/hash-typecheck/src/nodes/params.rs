use hash_tir::{context::Context, tir::ParamsId};

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

impl<E: TcEnv> OperationsOnNode<ParamsId> for Tc<'_, E> {
    type TyNode = ();

    fn check_node(
        &self,
        _ctx: &mut Context,
        _item: ParamsId,
        _item_ty: Self::TyNode,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise_node(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: ParamsId,
    ) -> NormaliseResult<ParamsId> {
        todo!()
    }

    fn unify_nodes(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: ParamsId,
        _target: ParamsId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: ParamsId) {
        todo!()
    }
}
