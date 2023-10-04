use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::tir::{DerefTerm, NodeId, NodeOrigin, RefTerm, RefTy, Term, TermId, Ty, TyId};

use crate::{
    diagnostics::TcError,
    env::TcEnv,
    options::normalisation::{
        normalise_nested, normalised_if, normalised_to, NormalisationState, NormaliseResult,
    },
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<RefTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ref_term: &mut RefTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let annotation_ref_ty = match *annotation_ty.value() {
            Ty::RefTy(ref_ty) => ref_ty,
            Ty::Hole(_) => RefTy {
                kind: ref_term.kind,
                mutable: ref_term.mutable,
                ty: Ty::hole_for(ref_term.subject),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        RefTy {
                            kind: ref_term.kind,
                            mutable: ref_term.mutable,
                            ty: Ty::hole(ref_term.subject.origin().inferred()),
                        },
                        original_term_id.origin().inferred(),
                    ),
                })
            }
        };

        self.check_node(ref_term.subject, annotation_ref_ty.ty)?;

        let ty =
            Ty::expect_is(original_term_id, Ty::from(annotation_ref_ty, annotation_ty.origin()));
        self.check_by_unify(ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: RefTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        normalise_nested()
    }

    fn unify(
        &self,
        r1: &mut RefTerm,
        r2: &mut RefTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        if r1.mutable != r2.mutable || r1.kind != r2.kind {
            return self.mismatching_atoms(src_node, target_node);
        }
        self.unify_nodes(r1.subject, r2.subject)
    }
}

impl<E: TcEnv> OperationsOn<DerefTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        deref_term: &mut DerefTerm,
        annotation_ty: Self::AnnotNode,
        _item_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        let deref_inner_inferred = Ty::hole_for(deref_term.subject);
        self.check_node(deref_term.subject, deref_inner_inferred)?;

        let dereferenced_ty = match *deref_inner_inferred.value() {
            Ty::RefTy(ref_ty) => ref_ty.ty,
            _ => {
                return Err(TcError::CannotDeref {
                    subject: deref_term.subject,
                    actual_subject_ty: deref_inner_inferred,
                })
            }
        };

        self.check_by_unify(dereferenced_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        mut deref_term: DerefTerm,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        let st = NormalisationState::new();
        deref_term.subject = self.normalise_node_and_record(deref_term.subject, &st)?;

        // Reduce:
        if let Term::Ref(ref_expr) = *deref_term.subject.value() {
            // Should never be effectful
            return normalised_to(ref_expr.subject);
        }

        normalised_if(|| Term::from(deref_term, item_node.origin().computed()), &st)
    }

    fn unify(
        &self,
        src: &mut DerefTerm,
        target: &mut DerefTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.unify_nodes(src.subject, target.subject)
    }
}

impl<E: TcEnv> OperationsOn<RefTy> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ref_ty: &mut RefTy,
        annotation_ty: Self::AnnotNode,
        _original_term_id: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // Infer the inner type
        self.check_node(ref_ty.ty, Ty::universe(NodeOrigin::Expected))?;
        self.check_is_universe(annotation_ty)?;
        Ok(())
    }

    fn try_normalise(&self, _: RefTy, _: Self::Node) -> NormaliseResult<ControlFlow<Self::Node>> {
        normalise_nested()
    }

    fn unify(
        &self,
        r1: &mut RefTy,
        r2: &mut RefTy,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        if r1.mutable != r2.mutable || r1.kind != r2.kind {
            return self.mismatching_atoms(src_node, target_node);
        }
        self.unify_nodes(r1.ty, r2.ty)
    }
}
