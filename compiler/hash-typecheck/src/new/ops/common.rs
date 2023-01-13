//! Contains operations that are common during typechecking and don't fit
//! anywhere else.
use crate::new::{diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv};

pub trait CommonOps: AccessToTcEnv {
    /// If the result is an error, add it to the diagnostics and return `None`.
    fn try_or_add_error<T>(&self, result: TcResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(error);
                None
            }
        }
    }
}

impl<T: AccessToTcEnv> CommonOps for T {}
