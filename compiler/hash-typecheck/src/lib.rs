#![feature(unwrap_infallible, never_type)]
use std::cell::RefCell;

use elaboration::ProofState;
use errors::{TcError, TcResult};
use hash_intrinsics::{intrinsics::AccessToIntrinsics, primitives::AccessToPrimitives};
use hash_reporting::diagnostic::{AccessToDiagnostics, Diagnostics};
use hash_tir::new::environment::env::AccessToEnv;
use infer::InferenceOps;
use substitution::ops::SubstitutionOps;
use unify::UnificationOps;

pub mod elaboration;
pub mod errors;
pub mod infer;
pub mod normalise;
pub mod substitution;
pub mod unify;

pub trait AccessToTypechecking:
    AccessToEnv + AccessToPrimitives + AccessToIntrinsics + AccessToDiagnostics + Sized
{
    fn proof_state(&self) -> &RefCell<ProofState>;

    fn convert_tc_error(
        &self,
        error: TcError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// If the result is an error, add it to the diagnostics and return `None`.
    fn try_or_add_error<T>(&self, result: TcResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(self.convert_tc_error(error));
                None
            }
        }
    }

    fn infer_ops(&self) -> InferenceOps<Self> {
        InferenceOps::new(self)
    }

    fn substitution_ops(&self) -> SubstitutionOps<Self> {
        SubstitutionOps::new(self)
    }

    fn unification_ops(&self) -> UnificationOps<Self> {
        UnificationOps::new(self)
    }
}
