use hash_tir::tir::{NodeOrigin, TermId, Ty, TyId, UniverseTy};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{already_normalised, NormalisationOptions},
        Operations,
    },
};

impl<E: TcEnv> Tc<'_, E> {
    pub fn check_is_universe(&self, ty: TyId) -> TcResult<()> {
        self.uni_ops().unify_terms(ty, Ty::universe(NodeOrigin::Expected))
    }
}

impl<E: TcEnv> Operations<UniverseTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(&self, _: &mut UniverseTy, item_ty: Self::TyNode, _: Self::Node) -> TcResult<()> {
        // Type: Type
        self.check_is_universe(item_ty)
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _: UniverseTy,
        _: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<TermId> {
        already_normalised()
    }

    fn unify(
        &self,
        _: &crate::operations::unification::UnificationOptions,
        _: &mut UniverseTy,
        _: &mut UniverseTy,
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        Ok(())
    }

    fn substitute(&self, _: &hash_tir::sub::Sub, _: &mut UniverseTy) {}
}
