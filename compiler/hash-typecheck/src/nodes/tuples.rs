use hash_tir::{
    context::Context,
    tir::{TermId, TupleTerm, TupleTy, TyId},
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

impl<E: TcEnv> Operations<TupleTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut TupleTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: TupleTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut TupleTerm,
        _target: &mut TupleTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TupleTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<TupleTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut TupleTy,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: TupleTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<TyId> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut TupleTy,
        _target: &mut TupleTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TupleTy) {
        todo!()
    }
}
