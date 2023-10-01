use hash_target::HasTarget;
use hash_tir::context::{Context, HasContext};
use hash_utils::{derive_more::Deref, state::LightState};

use crate::{
    env::{HasTcEnv, TcEnv},
    operations::{normalisation::NormalisationOptions, unification::UnificationOptions},
    substitution::SubstitutionOps,
};

/// The mode in which to infer the type of a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnInferMode {
    /// Infer the type of a function but do not look at its body.
    Header,
    /// Infer the type of a function and its body.
    Body,
}

/// This struct represents the typechecker.
///
/// It holds the state of the typechecker, which consists of
/// - the `TcEnv`, which is all the typechecker requires from the greater
///   environment of the compiler, to operate
/// - the `Context`, which is the current set of bindings the typechecker should
///   operate on.
#[derive(Deref)]
pub struct Tc<'tc, E> {
    #[deref]
    pub env: &'tc E,
    pub context: &'tc Context,
    pub fn_infer_mode: LightState<FnInferMode>,
    pub unification_opts: UnificationOptions,
    pub normalisation_opts: NormalisationOptions,
}

impl<E: TcEnv> Tc<'_, E> {
    pub fn sub_ops(&self) -> SubstitutionOps<E> {
        SubstitutionOps::new(self)
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

impl<E: TcEnv> HasTarget for Tc<'_, E> {
    fn target(&self) -> &hash_target::Target {
        self.env.target()
    }
}
