#![feature(
    unwrap_infallible,
    never_type,
    try_trait_v2,
    try_blocks,
    control_flow_enum,
    let_chains,
    if_let_guard
)]

use errors::{TcError, TcErrorState, TcResult};
use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_intrinsics::intrinsics::{AccessToIntrinsics, IntrinsicAbilities};
use hash_reporting::diagnostic::{AccessToDiagnostics, Diagnostics};
use hash_source::entry_point::EntryPointState;
use hash_tir::{
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    terms::TermId,
};
use inference::InferenceOps;
use substitution::SubstitutionOps;
use unification::UnificationOps;

pub mod errors;
pub mod inference;
pub mod normalisation;
pub mod params;
pub mod substitution;
pub mod unification;

pub trait AccessToTypechecking:
    AccessToEnv + AccessToIntrinsics + AccessToDiagnostics + Sized
{
    /// Convert a typechecking error to a diagnostic error.
    ///
    /// Provided by the implementer.
    fn convert_tc_error(
        &self,
        error: TcError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness error to a diagnostic error.
    fn convert_exhaustiveness_error(
        &self,
        error: ExhaustivenessError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness warning to a diagnostic warning.
    fn convert_exhaustiveness_warning(
        &self,
        warning: ExhaustivenessWarning,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Warning;

    /// Create a new error state.
    fn new_error_state(&self) -> TcErrorState {
        TcErrorState::new()
    }

    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool;

    /// Absorb an error state into the diagnostics.
    ///
    /// Returns the error or the closure result if successful.
    fn return_or_register_errors<T>(
        &self,
        t: impl FnOnce() -> TcResult<T>,
        mut error_state: TcErrorState,
    ) -> TcResult<T> {
        if error_state.has_errors() {
            Err(TcError::Compound { errors: error_state.take_errors() })
        } else {
            t()
        }
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

    fn norm_ops(&self) -> normalisation::NormalisationOps<Self> {
        normalisation::NormalisationOps::new(self)
    }

    fn param_ops(&self) -> params::ParamOps<Self> {
        params::ParamOps::new(self)
    }
}

pub struct IntrinsicAbilitiesWrapper<'tc, T: AccessToTypechecking> {
    tc: &'tc T,
}

impl<T: AccessToTypechecking> IntrinsicAbilities for IntrinsicAbilitiesWrapper<'_, T> {
    fn normalise_term(&self, term: TermId) -> Result<TermId, String> {
        let norm = self.tc.norm_ops();

        norm.normalise(term.into()).map(|result| norm.to_term(result)).map_err(|e| {
            self.tc.diagnostics().add_error(self.tc.convert_tc_error(e));
            "normalisation error".to_string()
        })
    }

    fn env(&self) -> &Env {
        self.tc.env()
    }
}
