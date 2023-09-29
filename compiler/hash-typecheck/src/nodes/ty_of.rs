use hash_tir::tir::{TermId, Ty, TyId, TyOfTerm};

use crate::{checker::Tc, env::TcEnv, operations::Operations};

impl<E: TcEnv> Operations<TyOfTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ty_of_term: &mut TyOfTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        let inferred_ty = Ty::hole_for(ty_of_term.term);
        self.infer_term(ty_of_term.term, inferred_ty)?;
        self.infer_term(inferred_ty, annotation_ty)?;
        self.norm_ops().normalise_in_place(original_term_id.into())?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: TyOfTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut TyOfTerm,
        _target: &mut TyOfTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TyOfTerm) {
        todo!()
    }
}
