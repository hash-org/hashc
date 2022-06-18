use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::error::{AnalysisError, AnalysisErrorKind, BlockOrigin};

mod block;
pub(super) mod error;
mod pat;

#[derive(Default)]
pub struct SemanticAnalyser {
    /// Whether the current visitor is within a loop construct.
    pub(crate) is_in_loop: bool,
    /// Whether the current visitor is within a function definition.
    pub(crate) is_in_function: bool,
    /// Any collected errors when passing through the tree
    pub(crate) errors: Vec<AnalysisError>,

    /// The current scope of the traversal, representing which block the analyser is walking.
    pub(crate) current_block: BlockOrigin,
}

impl SemanticAnalyser {
    /// Create a new semantic analyser
    pub fn new() -> Self {
        Self {
            is_in_loop: false,
            is_in_function: false,
            errors: vec![],
            current_block: BlockOrigin::Root,
        }
    }

    /// Function to check whether the current traversal state is within a constant block.
    /// This means that the [BlockOrigin] is currently not set to [BlockOrigin::Body].
    #[inline]
    pub(crate) fn is_in_constant_block(&self) -> bool {
        !matches!(self.current_block, BlockOrigin::Body)
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
