use hash_utils::derive_more::{Constructor, Deref};

use crate::env::TcEnv;

#[derive(Deref, Constructor)]
pub struct Checker<'env, E: TcEnv> {
    env: &'env E,
}
