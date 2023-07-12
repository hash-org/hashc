use hash_exhaustiveness::diagnostics::ExhaustivenessWarning;
use hash_reporting::reporter::{Reporter, Reports};
use hash_tir::environment::env::AccessToEnv;

use crate::environment::sem_env::WithSemEnv;

/// Warnings that can originate from the semantic analysis phase.
#[derive(Clone, Debug)]
pub enum SemanticWarning {
    /// A warning that comes from exhaustive pattern checking and
    /// analysis.
    ExhaustivenessWarning { warning: ExhaustivenessWarning },
}

impl From<ExhaustivenessWarning> for SemanticWarning {
    fn from(warning: ExhaustivenessWarning) -> Self {
        Self::ExhaustivenessWarning { warning }
    }
}

impl<'tc> From<WithSemEnv<'tc, &SemanticWarning>> for Reports {
    fn from(ctx: WithSemEnv<'tc, &SemanticWarning>) -> Self {
        let mut builder = Reporter::new();
        ctx.add_to_reporter(&mut builder);
        builder.into_reports()
    }
}

impl<'tc> WithSemEnv<'tc, &SemanticWarning> {
    /// Format the error nicely and add it to the given reporter.
    fn add_to_reporter(&self, reporter: &mut Reporter) {
        match self.value {
            SemanticWarning::ExhaustivenessWarning { warning } => {
                warning.add_to_reports(self.env(), reporter);
            }
        }
    }
}
