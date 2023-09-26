use hash_tir::{
    context::Context,
    tir::{TermId, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        OperationsOnNode,
    },
};

impl<E: TcEnv> OperationsOnNode<TermId> for Checker<'_, E> {
    type TyNode = TyId;

    fn check_node(
        &self,
        _ctx: &mut Context,
        _item: TermId,
        _item_ty: Self::TyNode,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise_node(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: TermId,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify_nodes(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: TermId,
        _target: TermId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: TermId) {
        todo!()
    }
}
