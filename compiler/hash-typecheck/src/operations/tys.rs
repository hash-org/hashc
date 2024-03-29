use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_tir::tir::{DataDefCtors, Ty, TyId};

use crate::{diagnostics::TcResult, env::TcEnv, tc::Tc, traits::OperationsOnNode};

impl<E: TcEnv> Tc<'_, E> {
    /// Given an inferred type, and an optional annotation type, unify the two,
    /// and if the result is successful then apply the substitution to the
    /// annotation type and return it (or to the inferred type if the annotation
    /// type is not given).
    pub fn check_by_unify(&self, inferred_ty: TyId, annotation_ty: TyId) -> TcResult<()> {
        self.unify_nodes(inferred_ty, annotation_ty)
    }

    /// Check that the given type is well-formed.
    pub fn check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Universe(_) | Ty::Meta(_) => Ok(()),
            _ => self.check_node(ty, Ty::universe_of(ty)),
        }
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<()> {
        self.check_node(ty, Ty::universe_of(ty))?;
        self.normalise_node_in_place_no_signals(ty)?;
        Ok(())
    }

    /// Determine whether the given type is uninhabitable.
    ///
    /// This does not look too deeply into the type, so it may return false
    /// for types that are actually uninhabitable.
    pub fn is_uninhabitable(&self, ty: TyId) -> TcResult<bool> {
        let ty = self.normalise_node_no_signals(ty)?;
        match *ty.value() {
            Ty::DataTy(data_ty) => {
                let data_def = data_ty.data_def.borrow();
                match data_def.ctors {
                    DataDefCtors::Defined(ctors) => Ok(ctors.len() == 0),
                    DataDefCtors::Primitive(_) => Ok(false),
                }
            }
            _ => Ok(false),
        }
    }
}
