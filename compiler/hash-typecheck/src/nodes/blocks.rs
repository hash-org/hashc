use hash_tir::{
    context::Context,
    scopes::BlockTerm,
    tir::{TermId, TyId},
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

impl<E: TcEnv> Operations<BlockTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut BlockTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: BlockTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut BlockTerm,
        _target: &mut BlockTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut BlockTerm) {
        todo!()
    }
}
