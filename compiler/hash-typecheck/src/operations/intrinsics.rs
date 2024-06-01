use std::ops::ControlFlow;

use hash_tir::{
    intrinsics::{definitions::Intrinsic, make::IsIntrinsic},
    tir::{NodeOrigin, Term, TermId, TyId},
};

use crate::{
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<Intrinsic> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        intrinsic: &mut Intrinsic,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // ##GeneratedOrigin: intrinsics do not belong to the source code
        self.unify_nodes(Term::from(intrinsic.ty(), NodeOrigin::Generated), annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: Intrinsic,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        already_normalised()
    }

    fn unify(
        &self,
        src: &mut Intrinsic,
        target: &mut Intrinsic,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.unification_ok_or_mismatching_atoms(*src == *target, src_node, target_node)
    }
}
