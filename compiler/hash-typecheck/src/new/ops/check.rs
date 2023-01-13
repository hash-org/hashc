//! Operations to perform type checking on terms.
use derive_more::Constructor;

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct CheckOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(CheckOps<'tc>);

impl<'tc> CheckOps<'tc> {}
