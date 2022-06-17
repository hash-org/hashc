use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::error::{AnalysisError, AnalysisErrorKind};

pub(super) mod error;
mod pat;

#[derive(Default)]
pub struct SemanticAnalyser {
    /// Whether the current visitor is within a loop construct.
    pub(super) is_in_loop: bool,
    /// Whether the current visitor is within a function definition.
    pub(super) _is_in_function: bool,
    /// Any collected errors when passing through the tree
    pub(super) errors: Vec<AnalysisError>,
}

impl SemanticAnalyser {
    /// Create a new semantic analyser
    pub fn new() -> Self {
        Self {
            is_in_loop: false,
            _is_in_function: false,
            errors: vec![],
        }
    }

    /// Append an error to the error queue.
    pub(crate) fn append_error(&mut self, error: AnalysisErrorKind, span: Span, id: SourceId) {
        self.errors
            .push(AnalysisError::new(error, SourceLocation::new(span, id)))
    }

    /// Return the collected errors from [SemanticAnalyser]
    pub fn errors(self) -> Vec<AnalysisError> {
        self.errors
    }
}
