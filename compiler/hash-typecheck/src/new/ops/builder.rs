use crate::{impl_access_to_tc_env, new::data::env::TcEnv};

pub struct Builder<'env> {
    env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(Builder<'env>);

impl<'env> Builder<'env> {}
