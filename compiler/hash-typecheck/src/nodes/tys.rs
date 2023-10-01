use hash_storage::store::statics::StoreId;
use hash_tir::tir::{Ty, TyId};

use crate::{checker::Tc, env::TcEnv, errors::TcResult, operations::OperationsOnNode};

impl<E: TcEnv> Tc<'_, E> {
    /// Given an inferred type, and an optional annotation type, unify the two,
    /// and if the result is successful then apply the substitution to the
    /// annotation type and return it (or to the inferred type if the annotation
    /// type is not given).
    pub fn check_by_unify(&self, inferred_ty: TyId, annotation_ty: TyId) -> TcResult<()> {
        self.uni_ops().unify_terms(inferred_ty, annotation_ty)
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Universe(_) | Ty::Hole(_) => Ok(()),
            _ => self.check_node(ty, Ty::universe_of(ty)),
        }
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Hole(_) => Ok(()),
            _ => {
                self.check_node(ty, Ty::universe_of(ty))?;
                let norm = self.norm_ops();
                norm.normalise_in_place(ty.into())?;
                Ok(())
            }
        }
    }
}
