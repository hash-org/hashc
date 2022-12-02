// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    environment::env::AccessToEnv,
    refs::RefTy,
    terms::{Term, TermId},
    tys::{Ty, TyId},
};
use hash_utils::store::{CloneStore, Store};

use super::common::CommonOps;
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::{
            error::{TcError, TcResult},
            panic::tc_panic_on_many,
        },
        environment::tc_env::TcEnv,
    },
};

#[derive(Constructor)]
pub struct Oracle<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(Oracle<'tc>);

impl<'tc> Oracle<'tc> {}
