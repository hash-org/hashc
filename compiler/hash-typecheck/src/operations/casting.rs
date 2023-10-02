use hash_tir::tir::{CastTerm, TermId, TyId};

use crate::{
    env::TcEnv,
    options::normalisation::normalised_option,
    tc::Tc,
    traits::{Operations, OperationsOnNode},
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
        cast_term: CastTerm,
        _: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<Self::Node> {
        // @@Todo: will not play well with typeof?;
        normalised_option(self.potentially_normalise(cast_term.subject_term)?)
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
}
