use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_pipeline::settings::HasCompilerSettings;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::HasTarget;
use hash_tir::{atom_info::HasAtomInfo, context::Context, tir::FnDefId};
use hash_utils::{state::LightState, timing::HasMetrics};

use crate::{
    errors::TcError,
    options::{normalisation::NormalisationOptions, unification::UnificationOptions},
    tc::{FnInferMode, Tc},
};

/// A wrapper trait around `HasDiagnostics` for specifically diagnostics that
/// can accomodate `TcError`s, `ExhaustivenessError`s and
/// `ExhaustivenessWarning`s. (and `TcWarning`s in the future.)
pub trait HasTcDiagnostics: HasDiagnostics<Diagnostics = Self::TcDiagnostics> {
    type ForeignError: From<TcError> + From<ExhaustivenessError>;
    type ForeignWarning: From<ExhaustivenessWarning>;
    type TcDiagnostics: Diagnostics<Error = Self::ForeignError, Warning = Self::ForeignWarning>;
}

/// The typechecking environment.
///
/// This trait declares all the required information that the typechecking stage
/// needs from the rest of the compiler in order to operate.
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

    /// Create a new typechecker using the given context.
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
