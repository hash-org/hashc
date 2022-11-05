use derive_more::Constructor;
use hash_types::new::{
    data::DataDefId,
    defs::DefParamsId,
    environment::env::AccessToEnv,
    mods::ModDefId,
    trts::TrtDefId,
    tys::{MetaTy, Ty, TyId},
};
use hash_utils::store::{CloneStore, SequenceStore};

use super::common::CommonOps;
use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct CommonDefOps<'env> {
    tc_env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(CommonDefOps<'tc>);

impl<'env> CommonDefOps<'env> {
    fn compute_fn_ty_of_some_def(&self, def_params_id: DefParamsId, final_ty: TyId) -> TyId {
        self.stores().def_params().map_fast(def_params_id, |def_params| {
            if !def_params.is_empty() {
                todo!("def with params not implemented")
            } else {
                final_ty
            }
        })
    }

    pub fn compute_fn_ty_of_data_def(&self, data_def_id: DataDefId) -> TyId {
        let data_def = self.stores().data_def().get(data_def_id);
        self.compute_fn_ty_of_some_def(data_def.params, self.new_small_universe_ty())
    }

    pub fn compute_fn_ty_of_trt_def(&self, trt_def_id: TrtDefId) -> TyId {
        let trt_def = self.stores().trt_def().get(trt_def_id);
        self.compute_fn_ty_of_some_def(trt_def.params, self.new_ty(Ty::Meta(MetaTy::TrtDefTy)))
    }

    pub fn compute_fn_ty_of_mod_def(&self, mod_def_id: ModDefId) -> TyId {
        let mod_def = self.stores().mod_def().get(mod_def_id);
        self.compute_fn_ty_of_some_def(mod_def.params, self.new_ty(Ty::Meta(MetaTy::ModDefTy)))
    }
}
