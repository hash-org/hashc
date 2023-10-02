use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    intrinsics::definitions::never_ty,
    scopes::AssignTerm,
    tir::{LoopControlTerm, LoopTerm, NodeId, NodeOrigin, ReturnTerm, Term, TermId, Ty, TyId},
};

use crate::{
    env::TcEnv,
    options::normalisation::{normalised_to, NormaliseResult, NormaliseSignal},
    tc::Tc,
    traits::{Operations, OperationsOnNode},
};

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
                self.check_node(return_term.expression, closest_fn_def_return_ty)?;

                let inferred_ty = Ty::expect_is(original_term_id, never_ty(NodeOrigin::Expected));
                self.check_by_unify(inferred_ty, annotation_ty)?;
                Ok(())
            }
            None => panic!("no fn def found in scope for return term"),
        }
    }

    fn try_normalise(
        &self,
        return_term: ReturnTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        let normalised = self.normalise_node(return_term.expression)?;
        Err(NormaliseSignal::Return(normalised))
    }

    fn unify(
        &self,
        _src: &mut ReturnTerm,
        _target: &mut ReturnTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
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

    fn try_normalise(
        &self,
        loop_control_term: LoopControlTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        match loop_control_term {
            LoopControlTerm::Break => Err(NormaliseSignal::Break),
            LoopControlTerm::Continue => Err(NormaliseSignal::Continue),
        }
    }

    fn unify(
        &self,
        _src: &mut LoopControlTerm,
        _target: &mut LoopControlTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
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
        self.check_node(loop_term.inner, Ty::hole(loop_term.inner.origin().inferred()))?;
        let loop_term =
            Ty::expect_is(original_term_id, Ty::unit_ty(original_term_id.origin().inferred()));
        self.check_by_unify(loop_term, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        loop_term: LoopTerm,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        loop {
            match self.normalise_node(loop_term.inner) {
                Ok(_) | Err(NormaliseSignal::Continue) => continue,
                Err(NormaliseSignal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        normalised_to(Term::unit(item_node.origin().computed()))
    }

    fn unify(
        &self,
        _src: &mut LoopTerm,
        _target: &mut LoopTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }
}

impl<E: TcEnv> Operations<AssignTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        assign_term: &mut AssignTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        let subject_ty = Ty::hole_for(assign_term.subject);
        self.check_node(assign_term.subject, subject_ty)?;

        let value_ty = Ty::hole_for(assign_term.value);
        self.check_node(assign_term.value, value_ty)?;

        self.check_by_unify(value_ty, subject_ty)?;

        let inferred_ty =
            Ty::expect_is(original_term_id, Ty::unit_ty(original_term_id.origin().inferred()));
        self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        mut assign_term: AssignTerm,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        assign_term.value = self.normalise_node(assign_term.value)?;

        match *assign_term.subject.value() {
            Term::Access(mut access_term) => {
                access_term.subject = self.normalise_node(access_term.subject)?;
                match *access_term.subject.value() {
                    Term::Tuple(tuple) => {
                        self.set_param_in_args(tuple.data, access_term.field, assign_term.value)
                    }
                    Term::Ctor(ctor) => {
                        self.set_param_in_args(ctor.ctor_args, access_term.field, assign_term.value)
                    }
                    _ => panic!("Invalid access"),
                }
            }
            Term::Var(var) => {
                self.context().modify_assignment(var.symbol, assign_term.value);
            }
            _ => panic!("Invalid assign {}", assign_term),
        }

        normalised_to(Term::unit(item_node.origin().computed()))
    }

    fn unify(
        &self,
        _src: &mut AssignTerm,
        _target: &mut AssignTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }
}
