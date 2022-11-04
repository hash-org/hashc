use super::env::TcEnv;
use crate::impl_access_to_tc_env;

pub struct Builder<'env> {
    env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(Builder<'env>);

impl<'env> Builder<'env> {}
