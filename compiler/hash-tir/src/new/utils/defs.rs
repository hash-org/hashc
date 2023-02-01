//! General definition-related utilities.
use derive_more::Constructor;

use crate::{impl_access_to_env, new::environment::env::Env};

/// Common definition-related operations.
#[derive(Constructor)]
pub struct DefUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(DefUtils<'tc>);

impl<'env> DefUtils<'env> {}
