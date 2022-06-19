use crossbeam_channel::Sender;
use hash_reporting::reporting::Report;
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::{
    error::{AnalysisError, AnalysisErrorKind, BlockOrigin},
    warning::{AnalysisWarning, AnalysisWarningKind},
};

mod block;
pub(crate) mod error;
mod pat;
pub(crate) mod warning;

/// Enum representing any generated message that can be emitted by the
/// [SemanticAnalyser].
pub(crate) enum AnalysisMessage {
    Warning(AnalysisWarning),
    Error(AnalysisError),
}

impl From<AnalysisMessage> for Report {
    fn from(message: AnalysisMessage) -> Self {
        match message {
            AnalysisMessage::Warning(warning) => warning.into(),
            AnalysisMessage::Error(err) => err.into(),
        }
    }
}

pub struct SemanticAnalyser {
    /// Whether the current visitor is within a loop construct.
    pub(crate) is_in_loop: bool,
    /// Whether the current visitor is within a function definition.
    pub(crate) is_in_function: bool,
    /// Any collected errors when passing through the tree.
    pub(crate) errors: Vec<AnalysisError>,
    /// Any collected warning that were found during the walk.
    pub(crate) warnings: Vec<AnalysisWarning>,
    /// The current id of the source that is being passed.
    pub(crate) source_id: SourceId,
    /// The current scope of the traversal, representing which block the analyser is walking.
    pub(crate) current_block: BlockOrigin,
}

impl SemanticAnalyser {
    /// Create a new semantic analyser
    pub fn new(source_id: SourceId) -> Self {
        Self {
            is_in_loop: false,
            is_in_function: false,
            errors: vec![],
            warnings: vec![],
            source_id,
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
    pub(crate) fn append_error(&mut self, error: AnalysisErrorKind, span: Span) {
        self.errors.push(AnalysisError::new(
            error,
            SourceLocation::new(span, self.source_id),
        ))
    }

    /// Append an warning to the warning queue.
    pub(crate) fn append_warning(&mut self, warning: AnalysisWarningKind, span: Span) {
        self.warnings.push(AnalysisWarning::new(
            warning,
            SourceLocation::new(span, self.source_id),
        ))
    }

    /// Given a [Sender], send all of the generated warnings and messaged into the sender.
    pub(crate) fn send_generated_messages(self, sender: &Sender<AnalysisMessage>) {
        self.errors
            .into_iter()
            .for_each(|err| sender.send(AnalysisMessage::Error(err)).unwrap());

        self.warnings
            .into_iter()
            .for_each(|warning| sender.send(AnalysisMessage::Warning(warning)).unwrap());
    }
}
