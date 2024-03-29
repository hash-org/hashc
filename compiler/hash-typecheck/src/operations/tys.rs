use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_tir::tir::{DataDefCtors, Ty, TyId};

use crate::{diagnostics::TcResult, env::TcEnv, tc::Tc, traits::OperationsOnNode};

impl<E: TcEnv> Tc<'_, E> {
    /// Check that the given type is well-formed.
    pub fn check_ty(&self, ty: TyId) -> TcResult<()> {
        let (resolved, _) = self.resolve_metas(ty); // @@Todo: what to do if type is a meta?
        match *resolved.value() {
            Ty::Universe(_) => Ok(()),
            _ => self.check_node(ty, Ty::universe_of(ty)),
        }
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
