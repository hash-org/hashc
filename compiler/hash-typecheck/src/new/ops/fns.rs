// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefData, FnDefId},
};
use hash_utils::store::Store;

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct FnOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(FnOps<'tc>);

impl<'tc> FnOps<'tc> {
    /// Create a function definition.
    pub fn create_fn_def(&self, data: FnDefData) -> FnDefId {
        self.stores().fn_def().create_with(|id| FnDef {
            id,
            name: data.name,
            ty: data.ty,
            body: data.body,
        })
    }
}
