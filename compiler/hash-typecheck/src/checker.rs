use hash_utils::derive_more::{Constructor, Deref};

use crate::env::{HasTcEnv, TcEnv};

#[derive(Deref, Constructor)]
pub struct Tc<'env, E: TcEnv> {
    env: &'env E,
}

impl<E: TcEnv> HasTcEnv for Tc<'_, E> {
    type Env = E;
    fn env(&self) -> &Self::Env {
        self.env
    }
}
