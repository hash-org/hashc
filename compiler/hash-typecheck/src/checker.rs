use hash_tir::context::{Context, HasContext};
use hash_utils::{derive_more::Deref, state::LightState};

use crate::{
    env::{HasTcEnv, TcEnv},
    inference::FnInferMode,
};

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
    pub fn_infer_mode: LightState<FnInferMode>,
}

impl<'tc, E: TcEnv> Tc<'tc, E> {
    pub fn new_in(env: &'tc E, context: &'tc Context, fn_infer_mode: FnInferMode) -> Self {
        Self { env, context, fn_infer_mode: LightState::new(fn_infer_mode) }
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
