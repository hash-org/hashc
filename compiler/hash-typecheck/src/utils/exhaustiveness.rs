use hash_exhaustiveness::ExhaustivenessChecker;
use hash_reporting::diagnostic::Diagnostics;
use hash_tir::tir::HasAstNodeId;

use crate::{env::TcEnv, tc::Tc};

impl<T: TcEnv> Tc<'_, T> {
    /// Create a new [ExhaustivenessChecker] so it can be used to check
    /// refutability or exhaustiveness of patterns.
    pub fn exhaustiveness_checker<U: HasAstNodeId>(&self, subject: U) -> ExhaustivenessChecker<T> {
        let location = subject.span().unwrap();
        ExhaustivenessChecker::new(location, self.env)
    }

    /// Merge all of the produced diagnostics into the current diagnostics.
    ///
    /// @@Hack: remove this when we have a better way to send exhaustiveness
    /// jobs and add them to general tc diagnostics.
    pub fn append_exhaustiveness_diagnostics(&self, checker: ExhaustivenessChecker<T>) {
        let (errors, warnings) = checker.into_diagnostics().into_diagnostics();

        for error in errors {
            self.diagnostics().add_error(error.into())
        }

        for warning in warnings {
            self.diagnostics().add_warning(warning.into())
        }
    }
}
