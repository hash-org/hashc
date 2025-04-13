use std::ops::ControlFlow;

use hash_tir::tir::{TermId, TyId, UnsafeTerm};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{NormaliseResult, normalised_option},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<UnsafeTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        unsafe_term: &mut UnsafeTerm,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> TcResult<()> {
        // @@Todo
        self.check_node(unsafe_term.inner, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        unsafe_term: UnsafeTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        // @@Todo
        normalised_option(self.potentially_normalise_node_no_signals(unsafe_term.inner)?)
    }

    fn unify(
        &self,
        src: &mut UnsafeTerm,
        target: &mut UnsafeTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.inner, target.inner)
    }
}
