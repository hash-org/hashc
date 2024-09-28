//! Contains the main typechecker structure, which holds the state of the
//! typechecker and is what all other `Operations` are implemented on.
use hash_ir::{HasIrCtx, IrCtx};
use hash_target::HasTarget;
use hash_tir::{
    context::{Context, HasContext},
    visitor::Visitor,
};
use hash_tir_utils::lower::{HasTyCache, TyCache, TyLowerEnv};
use hash_utils::{derive_more::Deref, state::LightState};

use crate::{
    env::{HasTcEnv, TcEnv},
    options::{normalisation::NormalisationOptions, unification::UnificationOptions},
    utils::substitution::Substituter,
};

/// The mode in which to infer the type of a function.
// @@Hack: this is currently a hack to get around the insufficient hole-filling
// mechanism of the typechecker. Ideally, we should eventually have a proper
// hole-filling mechanism which re-unifies things until everything is filled
// in. Then we can remove these two "inference passes" which are rather ad-hoc
// at the moment.
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
    pub in_pat: LightState<bool>,
}

impl<E: TcEnv> Tc<'_, E> {
    /// Convenience function to create a new TIR visitor.
    pub fn visitor(&self) -> Visitor {
        Visitor::new()
    }

    /// Create a substituter for this typechecker.
    pub fn substituter(&self) -> Substituter<E> {
        Substituter::new(self)
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

impl<E: TcEnv> HasIrCtx for Tc<'_, E> {
    fn ir_ctx(&self) -> &IrCtx {
        self.env.ir_ctx()
    }
}

impl<E: TcEnv> HasTyCache for Tc<'_, E> {
    fn repr_ty_cache(&self) -> &TyCache {
        self.env.repr_ty_cache()
    }
}

impl<E: TcEnv> HasTarget for Tc<'_, E> {
    fn target(&self) -> &hash_target::Target {
        self.env.target()
    }
}

impl<T: TcEnv> TyLowerEnv for Tc<'_, T> {}
