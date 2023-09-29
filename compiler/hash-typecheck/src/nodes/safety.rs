use hash_tir::tir::{TermId, TyId, UnsafeTerm};

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

impl<E: TcEnv> Operations<UnsafeTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        unsafe_term: &mut UnsafeTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> TcResult<()> {
        // @@Todo: unsafe context
        self.infer_term(unsafe_term.inner, annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: UnsafeTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut UnsafeTerm,
        _target: &mut UnsafeTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut UnsafeTerm) {
        todo!()
    }
}
