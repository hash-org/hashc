//! Hash AST semantic passes diagnostic definitions and logic.

use self::{error::AnalysisError, warning::AnalysisWarning};
use hash_reporting::report::Report;
use std::fmt::Display;

pub(crate) mod error;
pub(crate) mod warning;

/// Denotes where a pattern was used as in the parent of the pattern. This is useful
/// for propagating errors upwards by signalling what is the current parent of the
/// pattern. This only contains patterns that can be compound (hold multiple children patterns).
#[derive(Clone, Copy, Debug)]
pub(crate) enum PatternOrigin {
    Tuple,
    NamedField,
    Constructor,
    List,
    Namespace,
}

impl PatternOrigin {
    /// Convert the [PatternOrigin] into a string which can be used for displaying
    /// within error messages.
    fn to_str(self) -> &'static str {
        match self {
            PatternOrigin::Tuple => "tuple",
            PatternOrigin::NamedField => "named field",
            PatternOrigin::Constructor => "constructor",
            PatternOrigin::List => "list",
            PatternOrigin::Namespace => "namespace",
        }
    }
}

impl Display for PatternOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

/// Denotes where an error occurred from which type of block. This is useful
/// when giving more context about errors such as [AnalysisErrorKind::NonDeclarativeExpression]
/// occur from.
#[derive(Clone, Copy, Debug)]
pub(crate) enum BlockOrigin {
    Root,
    Mod,
    Impl,
    Body,
}

impl BlockOrigin {
    /// Convert the [BlockOrigin] into a string which can be used for displaying
    /// within error messages.
    fn to_str(self) -> &'static str {
        match self {
            BlockOrigin::Root | BlockOrigin::Mod => "module",
            BlockOrigin::Impl => "impl",
            BlockOrigin::Body => "body",
        }
    }
}

impl Default for BlockOrigin {
    fn default() -> Self {
        BlockOrigin::Root
    }
}

impl Display for BlockOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

/// Enum representing any generated message that can be emitted by the
/// [SemanticAnalyser].
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
