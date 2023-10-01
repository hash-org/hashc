use hash_tir::{
    intrinsics::{definitions::Intrinsic, make::IsIntrinsic},
    tir::{NodeOrigin, Term, TermId, TyId},
};

use crate::{env::TcEnv, tc::Tc, traits::Operations};

impl<E: TcEnv> Operations<Intrinsic> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        intrinsic: &mut Intrinsic,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        // ##GeneratedOrigin: intrinsics do not belong to the source code
        self.check_by_unify(Term::from(intrinsic.ty(), NodeOrigin::Generated), annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _item: Intrinsic,
        _item_node: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _src: &mut Intrinsic,
        _target: &mut Intrinsic,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }
}
