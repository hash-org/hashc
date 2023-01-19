//! General definition-related utilities.
use derive_more::Constructor;
use hash_utils::store::{CloneStore, SequenceStore};

use super::common::CommonUtils;
use crate::{
    impl_access_to_env,
    new::{
        data::DataDefId,
        defs::DefParamsId,
        environment::env::{AccessToEnv, Env},
        tys::TyId,
    },
};

/// Common definition-related operations.
#[derive(Constructor)]
pub struct DefUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(DefUtils<'tc>);

impl<'env> DefUtils<'env> {
    /// Compute the function type of some definition with final type `T`.
    ///
    /// If the definition has parameters `(A1: B1) ... (AN: BN)`, then the
    /// function type will be `(A1:B1) -> ... -> (AN:BN) -> T`.
    fn compute_fn_ty_of_some_def(&self, def_params_id: DefParamsId, final_ty: TyId) -> TyId {
        self.stores().def_params().map_fast(def_params_id, |def_params| {
            if !def_params.is_empty() {
                todo!("def with params not implemented")
            } else {
                final_ty
            }
        })
    }

    /// Compute the function type of some data definition, which is
    /// `compute_fn_ty_of_some_def` where `T = Type`.
    pub fn compute_fn_ty_of_data_def(&self, data_def_id: DataDefId) -> TyId {
        let data_def = self.stores().data_def().get(data_def_id);
        self.compute_fn_ty_of_some_def(data_def.params, self.new_small_universe_ty())
    }
}
