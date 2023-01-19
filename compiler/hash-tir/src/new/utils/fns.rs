//! Function-related utilities.
use derive_more::Constructor;
use hash_utils::store::Store;

use crate::{
    impl_access_to_env,
    new::{
        environment::env::{AccessToEnv, Env},
        fns::{FnDef, FnDefData, FnDefId},
    },
};

#[derive(Constructor)]
pub struct FnUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(FnUtils<'tc>);

impl<'tc> FnUtils<'tc> {
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
