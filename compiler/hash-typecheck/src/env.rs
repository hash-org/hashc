use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_pipeline::settings::HasCompilerSettings;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::HasTarget;
use hash_tir::{atom_info::HasAtomInfo, context::Context, tir::FnDefId};
use hash_utils::{state::LightState, timing::HasMetrics};

use crate::{
    checker::{FnInferMode, Tc},
    errors::TcError,
    operations::{normalisation::NormalisationOptions, unification::UnificationOptions},
};

pub trait HasTcDiagnostics: HasDiagnostics<Diagnostics = Self::TcDiagnostics> {
    type ForeignError: From<TcError> + From<ExhaustivenessError>;
    type ForeignWarning: From<ExhaustivenessWarning>;
    type TcDiagnostics: Diagnostics<Error = Self::ForeignError, Warning = Self::ForeignWarning>;
}

pub trait TcEnv:
    HasTcDiagnostics + HasTarget + HasAtomInfo + HasCompilerSettings + HasMetrics + Sized
{
    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// The current source ID.
    fn current_source(&self) -> SourceId;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool {
        self.settings().semantic_settings.mono_tir
    }

    fn checker<'a>(&'a self, context: &'a Context) -> Tc<Self> {
        Tc {
            env: self,
            context,
            fn_infer_mode: LightState::new(FnInferMode::Body),
            unification_opts: UnificationOptions::default(),
            normalisation_opts: NormalisationOptions::default(),
        }
    }
}

pub trait HasTcEnv {
    type Env: TcEnv;
    fn env(&self) -> &Self::Env;
}
