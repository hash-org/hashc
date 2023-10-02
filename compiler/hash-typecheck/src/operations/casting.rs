use std::ops::ControlFlow;

use hash_tir::tir::{CastTerm, TermId, TyId};

use crate::{
    env::TcEnv,
    options::normalisation::{normalised_option, NormaliseResult},
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

    fn try_normalise(
        &self,
        cast_term: CastTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        // @@Todo: will not play well with typeof?;
        normalised_option(self.potentially_normalise_node_no_signals(cast_term.subject_term)?)
    }

    fn unify(
        &self,
        src: &mut CastTerm,
        target: &mut CastTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        self.unify_nodes(src.subject_term, target.subject_term)?;
        self.unify_nodes(src.target_ty, target.target_ty)
    }
}
