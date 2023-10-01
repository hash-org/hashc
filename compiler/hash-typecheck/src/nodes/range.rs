use hash_tir::tir::{PatId, RangePat, TyId};

use crate::{
    checker::Tc,
    env::TcEnv,
    operations::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<RangePat> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        range_pat: &mut RangePat,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        let RangePat { lo, hi, .. } = range_pat;

        lo.map(|lo| self.check_node(*lo, annotation_ty)).transpose()?;
        hi.map(|hi| self.check_node(*hi, annotation_ty)).transpose()?;

        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: RangePat,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut RangePat,
        _target: &mut RangePat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut RangePat) {
        todo!()
    }
}
