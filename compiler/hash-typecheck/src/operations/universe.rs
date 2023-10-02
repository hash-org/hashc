use hash_tir::tir::{NodeOrigin, TermId, Ty, TyId, UniverseTy};

use crate::{
    env::TcEnv,
    errors::TcResult,
    options::normalisation::already_normalised,
    tc::Tc,
    traits::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    pub fn check_is_universe(&self, ty: TyId) -> TcResult<()> {
        self.unify_nodes(ty, Ty::universe(NodeOrigin::Expected))
    }
}

impl<E: TcEnv> Operations<UniverseTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(&self, _: &mut UniverseTy, item_ty: Self::TyNode, _: Self::Node) -> TcResult<()> {
        // Type: Type
        self.check_is_universe(item_ty)
    }

    fn try_normalise(
        &self,
        _: UniverseTy,
        _: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<TermId> {
        already_normalised()
    }

    fn unify(
        &self,
        _: &mut UniverseTy,
        _: &mut UniverseTy,
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        Ok(())
    }
}
