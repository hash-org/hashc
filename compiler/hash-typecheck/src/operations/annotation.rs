use std::ops::ControlFlow;

use hash_tir::tir::{AnnotTerm, TermId, TyId};

use crate::{
    env::TcEnv,
    options::normalisation::{normalised_option, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<AnnotTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        cast_term: &mut AnnotTerm,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.check_node(cast_term.subject_term, cast_term.target_ty)?;
        self.check_by_unify(cast_term.target_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        cast_term: AnnotTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        // @@Todo: will not play well with typeof?;
        normalised_option(self.potentially_normalise_node_no_signals(cast_term.subject_term)?)
    }

    fn unify(
        &self,
        src: &mut AnnotTerm,
        target: &mut AnnotTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.unify_nodes(src.subject_term, target.subject_term)?;
        self.unify_nodes(src.target_ty, target.target_ty)
    }
}
