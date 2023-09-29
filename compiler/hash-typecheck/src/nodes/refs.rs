use hash_storage::store::statics::StoreId;
use hash_tir::tir::{DerefTerm, TermId, Ty, TyId};

use crate::{checker::Tc, env::TcEnv, errors::TcError, operations::Operations};

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
