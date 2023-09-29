use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    intrinsics::definitions::never_ty,
    tir::{LoopControlTerm, LoopTerm, NodeId, NodeOrigin, ReturnTerm, TermId, Ty, TyId},
};

use crate::{checker::Tc, env::TcEnv, operations::Operations};

impl<E: TcEnv> Operations<ReturnTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        return_term: &mut ReturnTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        let closest_fn_def = self.context().get_first_fn_def_in_scope();
        match closest_fn_def {
            Some(closest_fn_def) => {
                // Get the closest fn def in scope, and unify the
                // inferred expression type with its return type.
                // If successful, modify the fn def to set the return type to the inferred type.
                let closest_fn_def_return_ty = closest_fn_def.borrow().ty.return_ty;
                self.infer_term(return_term.expression, closest_fn_def_return_ty)?;

                let inferred_ty = Ty::expect_is(original_term_id, never_ty(NodeOrigin::Expected));
                self.check_by_unify(inferred_ty, annotation_ty)?;
                Ok(())
            }
            None => panic!("no fn def found in scope for return term"),
        }
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: ReturnTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut ReturnTerm,
        _target: &mut ReturnTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ReturnTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<LoopControlTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _: &mut LoopControlTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        // Always `never`.
        self.check_by_unify(never_ty(NodeOrigin::Expected), annotation_ty)
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: LoopControlTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut LoopControlTerm,
        _target: &mut LoopControlTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut LoopControlTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<LoopTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        loop_term: &mut LoopTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        // Forward to the inner term.
        self.infer_term(loop_term.inner, Ty::hole(loop_term.inner.origin().inferred()))?;
        let loop_term =
            Ty::expect_is(original_term_id, Ty::unit_ty(original_term_id.origin().inferred()));
        self.check_by_unify(loop_term, annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: LoopTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut LoopTerm,
        _target: &mut LoopTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut LoopTerm) {
        todo!()
    }
}
