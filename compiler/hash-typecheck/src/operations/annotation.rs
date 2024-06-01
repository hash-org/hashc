use std::ops::ControlFlow;

use hash_tir::tir::{AnnotTerm, NodeId, Term, TermId, Ty, TyId};

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
        self.check_node(cast_term.target_ty, Ty::universe_of(cast_term.target_ty))?;
        self.check_node(cast_term.subject_term, cast_term.target_ty)?;
        self.unify_nodes(cast_term.target_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        cast_term: AnnotTerm,
        original_term_id: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        let subject_term = self.potentially_normalise_node_no_signals(cast_term.subject_term)?;
        let target_ty = self.potentially_normalise_node_no_signals(cast_term.target_ty)?;
        normalised_option(
            try {
                Term::from(
                    AnnotTerm { subject_term: subject_term?, target_ty: target_ty? },
                    original_term_id.origin().computed(),
                )
            },
        )
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
