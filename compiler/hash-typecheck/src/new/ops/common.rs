// @@Docs
use crate::new::{diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv};

/// Common operations during typechecking.
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
