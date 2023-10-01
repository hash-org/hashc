use hash_tir::tir::{CastTerm, TermId, TyId};

use crate::{
    checker::Tc,
    env::TcEnv,
    operations::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<CastTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        cast_term: &mut CastTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        self.check_node(cast_term.subject_term, cast_term.target_ty)?;
        self.check_by_unify(cast_term.target_ty, annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _item: CastTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _src: &mut CastTerm,
        _target: &mut CastTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut CastTerm) {
        todo!()
    }
}
