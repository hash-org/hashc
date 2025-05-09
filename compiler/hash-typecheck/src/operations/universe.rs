use std::ops::ControlFlow;

use hash_tir::tir::{NodeOrigin, TermId, Ty, TyId, UniverseTy};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{NormaliseResult, already_normalised},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    pub fn check_is_universe(&self, ty: TyId) -> TcResult<()> {
        self.unify_nodes(ty, Ty::universe(NodeOrigin::Expected))
    }
}

impl<E: TcEnv> OperationsOn<UniverseTy> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TyId;

    fn check(&self, _: &mut UniverseTy, item_ty: Self::AnnotNode, _: Self::Node) -> TcResult<()> {
        // Type: Type
        self.check_is_universe(item_ty)
    }

    fn try_normalise(&self, _: UniverseTy, _: Self::Node) -> NormaliseResult<ControlFlow<TermId>> {
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
