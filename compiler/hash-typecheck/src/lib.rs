use std::cell::RefCell;

use elaboration::ProofState;
use errors::{TcError, TcResult};
use hash_intrinsics::{intrinsics::AccessToIntrinsics, primitives::AccessToPrimitives};
use hash_reporting::diagnostic::{AccessToDiagnostics, Diagnostics};
use hash_tir::new::environment::env::AccessToEnv;

pub mod elaboration;
pub mod errors;
pub mod infer;
pub mod normalise;
pub mod subs;
pub mod substitutions;
pub mod unify;

pub trait AccessToTypechecking:
    AccessToEnv + AccessToPrimitives + AccessToIntrinsics + AccessToDiagnostics + Sized
{
    fn proof_state(&self) -> &RefCell<ProofState>;

    fn convert_tc_error(&self, error: TcError) -> Self::Error;

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

    fn infer_ops(&self) -> infer::InferOps<Self> {
        infer::InferOps::new(self)
    }
}
