use hash_tir::tir::{TermId, Ty, TyId, TyOfTerm};

use crate::{
    env::TcEnv,
    tc::Tc,
    utils::operation_traits::{Operations, OperationsOnNode},
};

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
        self.check_node(ty_of_term.term, inferred_ty)?;
        self.check_node(inferred_ty, annotation_ty)?;
        self.normalise_in_place(original_term_id.into())?;
        Ok(())
    }

    fn normalise(
        &self,

        _item: TyOfTerm,
        _item_node: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,

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
