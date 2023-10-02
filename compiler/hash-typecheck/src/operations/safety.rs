use hash_tir::tir::{TermId, TyId, UnsafeTerm};

use crate::{
    env::TcEnv,
    errors::TcResult,
    options::normalisation::{normalised_option, NormaliseResult},
    tc::Tc,
    traits::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<UnsafeTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        unsafe_term: &mut UnsafeTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> TcResult<()> {
        // @@Todo
        self.check_node(unsafe_term.inner, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(&self, unsafe_term: UnsafeTerm, _: Self::Node) -> NormaliseResult<TermId> {
        // @@Todo
        normalised_option(self.potentially_normalise_node_no_signals(unsafe_term.inner)?)
    }

    fn unify(
        &self,
        _src: &mut UnsafeTerm,
        _target: &mut UnsafeTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }
}
