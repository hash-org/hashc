use hash_intrinsics::{primitives::DefinedPrimitives, utils::IntrinsicUtils};

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

    /// Access the primitive definitions.
    fn primitives(&self) -> &DefinedPrimitives {
        match self.primitives_or_unset().get() {
            Some(primitives) => primitives,
            None => panic!("called primitives() before they were set"),
        }
    }

    fn intrinsic_utils(&self) -> IntrinsicUtils {
        IntrinsicUtils::new(self.env(), self.primitives())
    }
}

impl<T: AccessToTcEnv> CommonOps for T {}
