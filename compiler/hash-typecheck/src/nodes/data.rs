use hash_tir::tir::{CtorTerm, DataTy, TermId, TyId};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<CtorTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,

        _item: &mut CtorTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,

        _opts: &NormalisationOptions,
        _item: CtorTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,

        _opts: &UnificationOptions,
        _src: &mut CtorTerm,
        _target: &mut CtorTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut CtorTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<DataTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,

        _item: &mut DataTy,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,

        _opts: &NormalisationOptions,
        _item: DataTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<TyId> {
        todo!()
    }

    fn unify(
        &self,

        _opts: &UnificationOptions,
        _src: &mut DataTy,
        _target: &mut DataTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut DataTy) {
        todo!()
    }
}
