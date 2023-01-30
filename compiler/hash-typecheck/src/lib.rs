#![feature(unwrap_infallible, never_type, try_trait_v2, try_blocks)]

use errors::{TcError, TcErrorState, TcResult};
use hash_intrinsics::{intrinsics::AccessToIntrinsics, primitives::AccessToPrimitives};
use hash_reporting::diagnostic::{AccessToDiagnostics, Diagnostics};
use hash_tir::new::environment::env::AccessToEnv;
use inference::InferenceOps;
use substitution::SubstitutionOps;
use unification::UnificationOps;

pub mod errors;
pub mod inference;
pub mod normalisation;
pub mod substitution;
pub mod unification;

pub trait AccessToTypechecking:
    AccessToEnv + AccessToPrimitives + AccessToIntrinsics + AccessToDiagnostics + Sized
{
    /// Convert a typechecking error to a diagnostic error.
    ///
    /// Provided by the implementor.
    fn convert_tc_error(
        &self,
        error: TcError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Create a new error state.
    fn new_error_state(&self) -> TcErrorState {
        TcErrorState::new()
    }

    /// Absorb an error state into the diagnostics.
    ///
    /// Returns the error or the closure result if successful.
    fn return_or_register_errors<T>(
        &self,
        t: impl FnOnce() -> TcResult<T>,
        mut error_state: TcErrorState,
    ) -> TcResult<T> {
        if error_state.has_errors() {
            error_state.take_errors().into_iter().for_each(|error| {
                self.diagnostics().add_error(self.convert_tc_error(error));
            });
            if error_state.has_blocked {
                Err(TcError::Blocked)
            } else {
                Err(TcError::Signal)
            }
        } else {
            t()
        }
    }

    fn inference_ops(&self) -> InferenceOps<Self> {
        InferenceOps::new(self)
    }

    fn substitution_ops(&self) -> SubstitutionOps<Self> {
        SubstitutionOps::new(self)
    }

    fn unification_ops(&self) -> UnificationOps<Self> {
        UnificationOps::new(self)
    }

    fn normalisation_ops(&self) -> normalisation::NormalisationOps<Self> {
        normalisation::NormalisationOps::new(self)
    }
}
