//! Contains operations that are common during typechecking and don't fit
//! anywhere else.

use hash_reporting::diagnostic::Diagnostics;

use crate::{diagnostics::error::SemanticResult, environment::sem_env::AccessToSemEnv};

pub trait CommonOps: AccessToSemEnv {
    /// If the result is an error, add it to the diagnostics and return `None`.
    fn try_or_add_error<T>(&self, result: SemanticResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(error);
                None
            }
        }
    }
}

impl<T: AccessToSemEnv> CommonOps for T {}
