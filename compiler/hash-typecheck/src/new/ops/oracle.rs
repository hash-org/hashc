// @@Docs
use derive_more::Constructor;

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct Oracle<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(Oracle<'tc>);

impl<'tc> Oracle<'tc> {}
