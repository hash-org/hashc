//! Hash AST semantic passes diagnostic definitions and logic.
#![allow(dead_code)]

use self::{error::AnalysisError, warning::AnalysisWarning};
use hash_reporting::report::Report;

pub(crate) mod directives;
pub(crate) mod error;
pub(crate) mod origins;
pub(crate) mod warning;

/// Enum representing any generated message that can be emitted by the
/// [crate::SemanticAnalyser].
pub(crate) enum Diagnostic {
    Warning(AnalysisWarning),
    Error(AnalysisError),
}

impl From<Diagnostic> for Report {
    fn from(message: Diagnostic) -> Self {
        match message {
            Diagnostic::Warning(warning) => warning.into(),
            Diagnostic::Error(err) => err.into(),
        }
    }
}
