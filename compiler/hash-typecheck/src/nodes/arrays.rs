use hash_tir::{
    context::Context,
    tir::{ArrayPat, ArrayTerm, PatId, TermId, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::CheckResult,
        normalisation::NormaliseResult,
        unification::{UnificationOptions, UnifyResult},
        Operations,
    },
};

impl<E: TcEnv> Operations<ArrayTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut ArrayTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut ArrayTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut ArrayTerm,
        _target: &mut ArrayTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ArrayTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<ArrayPat> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut ArrayPat,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut ArrayPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: &mut ArrayPat,
        _target: &mut ArrayPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ArrayPat) {
        todo!()
    }
}
