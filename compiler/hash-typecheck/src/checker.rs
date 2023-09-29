use hash_tir::context::{Context, HasContext};
use hash_utils::derive_more::Deref;

use crate::env::{HasTcEnv, TcEnv};

/// This struct represents the typechecker.
///
/// It holds the state of the typechecker, which consists of
/// - the `TcEnv`, which is all the typechecker requires from the greater
///   environment of the compiler, to operate
/// - the `Context`, which is the current set of bindings the typechecker should
///   operate on.
#[derive(Deref)]
pub struct Tc<'tc, E: TcEnv> {
    #[deref]
    pub env: &'tc E,
    pub context: &'tc Context,
}

impl<'tc, E: TcEnv> Tc<'tc, E> {
    pub fn new_in(env: &'tc E, context: &'tc Context) -> Self {
        Self { env, context }
    }
}

impl<E: TcEnv> HasTcEnv for Tc<'_, E> {
    type Env = E;
    fn env(&self) -> &Self::Env {
        self.env
    }
}

impl<E: TcEnv> HasContext for Tc<'_, E> {
    fn context(&self) -> &Context {
        self.context
    }
}
