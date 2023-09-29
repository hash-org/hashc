use hash_storage::store::statics::StoreId;
use hash_tir::tir::{DerefTerm, NodeId, NodeOrigin, RefTerm, RefTy, TermId, Ty, TyId};

use crate::{checker::Tc, env::TcEnv, errors::TcError, operations::Operations};

impl<E: TcEnv> Operations<RefTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ref_term: &mut RefTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
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

        self.infer_term(ref_term.subject, annotation_ref_ty.ty)?;

        let ty =
            Ty::expect_is(original_term_id, Ty::from(annotation_ref_ty, annotation_ty.origin()));
        self.check_by_unify(ty, annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: RefTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut RefTerm,
        _target: &mut RefTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut RefTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<DerefTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        deref_term: &mut DerefTerm,
        annotation_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        let deref_inner_inferred = Ty::hole_for(deref_term.subject);
        self.infer_term(deref_term.subject, deref_inner_inferred)?;

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

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: DerefTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut DerefTerm,
        _target: &mut DerefTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut DerefTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<RefTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        ref_ty: &mut RefTy,
        annotation_ty: Self::TyNode,
        _original_term_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        // Infer the inner type
        self.infer_term(ref_ty.ty, Ty::universe(NodeOrigin::Expected))?;
        self.check_is_universe(annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: RefTy,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut RefTy,
        _target: &mut RefTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut RefTy) {
        todo!()
    }
}
