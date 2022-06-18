use crossbeam_channel::Sender;
use hash_reporting::reporting::Report;
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::{
    error::{AnalysisError, AnalysisErrorKind},
    warning::{AnalysisWarning, AnalysisWarningKind},
};

mod block;
pub(super) mod error;
mod pat;
pub(super) mod warning;

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

#[derive(Default)]
pub struct SemanticAnalyser {
    /// Whether the current visitor is within a loop construct.
    pub(super) is_in_loop: bool,
    /// Whether the current visitor is within a function definition.
    pub(super) is_in_function: bool,
    /// Any collected errors when passing through the tree.
    pub(super) errors: Vec<AnalysisError>,
    /// Any collected warning that were found during the walk.
    pub(super) warnings: Vec<AnalysisWarning>,
}

impl SemanticAnalyser {
    /// Create a new semantic analyser
    pub fn new() -> Self {
        Self {
            is_in_loop: false,
            is_in_function: false,
            errors: vec![],
            warnings: vec![],
        }
    }

    /// Append an error to the error queue.
    pub(crate) fn append_error(&mut self, error: AnalysisErrorKind, span: Span, id: SourceId) {
        self.errors
            .push(AnalysisError::new(error, SourceLocation::new(span, id)))
    }

    /// Append an warning to the warning queue.
    pub(crate) fn append_warning(
        &mut self,
        warning: AnalysisWarningKind,
        span: Span,
        id: SourceId,
    ) {
        self.warnings
            .push(AnalysisWarning::new(warning, SourceLocation::new(span, id)))
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
