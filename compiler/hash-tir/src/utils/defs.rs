//! General definition-related utilities.
use derive_more::Constructor;

use crate::{environment::env::Env, impl_access_to_env};

/// Common definition-related operations.
#[derive(Constructor)]
pub struct DefUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(DefUtils<'tc>);

impl<'env> DefUtils<'env> {}
