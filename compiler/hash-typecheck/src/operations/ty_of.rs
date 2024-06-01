use std::ops::ControlFlow;

use hash_tir::{
    atom_info::ItemInAtomInfo,
    tir::{TermId, TyId, TyOfTerm},
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{normalised_to, stuck_normalising, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<TyOfTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ty_of_term: &mut TyOfTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let inferred_ty = self.fresh_meta_for(ty_of_term.term);
        self.check_node(ty_of_term.term, inferred_ty)?;
        self.check_node(inferred_ty, annotation_ty)?;
        self.normalise_node_in_place_no_signals(original_term_id)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        ty_of_term: TyOfTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        // Infer the type of the term:
        match self.try_get_inferred_ty(ty_of_term.term) {
            Some(ty) => normalised_to(ty),
            None => {
                // Not evaluated yet
                stuck_normalising()
            }
        }
    }

    fn unify(
        &self,
        src: &mut TyOfTerm,
        target: &mut TyOfTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.term, target.term)
    }
}
