use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_pipeline::settings::HasCompilerSettings;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::HasTarget;
use hash_tir::{atom_info::HasAtomInfo, context::HasContext, tir::FnDefId};
use hash_utils::timing::HasMetrics;

use crate::{
    checker::Tc,
    errors::TcError,
    inference::InferenceOps,
    normalisation,
    operations::{normalisation::NormalisationOptions, unification::UnificationOptions},
    substitution::SubstitutionOps,
    unification::UnificationOps,
};

pub trait HasTcDiagnostics: HasDiagnostics<Diagnostics = Self::TcDiagnostics> {
    type ForeignError: From<TcError> + From<ExhaustivenessError>;
    type ForeignWarning: From<ExhaustivenessWarning>;
    type TcDiagnostics: Diagnostics<Error = Self::ForeignError, Warning = Self::ForeignWarning>;
}

pub trait TcEnv:
    HasTcDiagnostics + HasTarget + HasContext + HasAtomInfo + HasCompilerSettings + HasMetrics + Sized
{
    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// The current source ID.
    fn current_source(&self) -> SourceId;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool {
        self.settings().semantic_settings.mono_tir
    }

    fn checker(&self) -> Tc<Self> {
        Tc::new(self)
    }

    fn infer_ops(&self) -> InferenceOps<Self> {
        InferenceOps::new(self)
    }

    fn sub_ops(&self) -> SubstitutionOps<Self> {
        SubstitutionOps::new(self)
    }

    fn uni_ops(&self) -> UnificationOps<Self> {
        UnificationOps::new(self)
    }

    fn uni_ops_with<'a>(&'a self, opts: &'a UnificationOptions) -> UnificationOps<Self> {
        UnificationOps::new_with_opts(self, opts)
    }

    fn norm_ops(&self) -> normalisation::NormalisationOps<Self> {
        normalisation::NormalisationOps::new(self)
    }

    fn norm_ops_with<'a>(
        &'a self,
        opts: &'a NormalisationOptions,
    ) -> normalisation::NormalisationOps<Self> {
        normalisation::NormalisationOps::new_with_opts(self, opts)
    }
}

pub trait HasTcEnv {
    type Env: TcEnv;
    fn env(&self) -> &Self::Env;
}
