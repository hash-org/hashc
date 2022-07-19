//! Hash semantic analyser definitions. This file holds the [SemanticAnalyser]
//! definition with some shared functions to append diagnostics to the analyser.

use crossbeam_channel::Sender;
use hash_source::{
    location::{SourceLocation, Span},
    SourceId, SourceMap,
};

use crate::diagnostics::{
    error::{AnalysisError, AnalysisErrorKind},
    origins::BlockOrigin,
    warning::{AnalysisWarning, AnalysisWarningKind},
    Diagnostic,
};

mod block;
mod pat;

pub struct SemanticAnalyser<'s> {
    /// Whether the current visitor is within a loop construct.
    pub(crate) is_in_loop: bool,
    /// Whether the current visitor is within a function definition.
    pub(crate) is_in_fn: bool,
    /// Any collected errors when passing through the tree.
    pub(crate) errors: Vec<AnalysisError>,
    /// Any collected warning that were found during the walk.
    pub(crate) warnings: Vec<AnalysisWarning>,
    /// The current id of the source that is being passed.
    pub(crate) source_id: SourceId,
    /// A reference to the sources of the current job.
    pub(crate) source_map: &'s SourceMap,
    /// The current scope of the traversal, representing which block the
    /// analyser is walking.
    pub(crate) current_block: BlockOrigin,
}

impl<'s> SemanticAnalyser<'s> {
    /// Create a new semantic analyser
    pub fn new(source_map: &'s SourceMap, source_id: SourceId) -> Self {
        Self {
            is_in_loop: false,
            is_in_fn: false,
            errors: vec![],
            warnings: vec![],
            source_id,
            source_map,
            current_block: BlockOrigin::Root,
        }
    }

    /// Function to check whether the current traversal state is within a
    /// constant block. This means that the [BlockOrigin] is currently not
    /// set to [BlockOrigin::Body].
    #[inline]
    pub(crate) fn is_in_constant_block(&self) -> bool {
        !matches!(self.current_block, BlockOrigin::Body)
    }

    /// Append an error to the error queue.
    pub(crate) fn append_error(&mut self, error: AnalysisErrorKind, span: Span) {
        self.errors.push(AnalysisError::new(error, SourceLocation::new(span, self.source_id)))
    }

    /// Append an warning to the warning queue.
    pub(crate) fn append_warning(&mut self, warning: AnalysisWarningKind, span: Span) {
        self.warnings.push(AnalysisWarning::new(warning, SourceLocation::new(span, self.source_id)))
    }

    /// Given a [Sender], send all of the generated warnings and messaged into
    /// the sender.
    pub(crate) fn send_generated_messages(self, sender: &Sender<Diagnostic>) {
        self.errors.into_iter().for_each(|err| sender.send(Diagnostic::Error(err)).unwrap());

        self.warnings
            .into_iter()
            .for_each(|warning| sender.send(Diagnostic::Warning(warning)).unwrap());
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, source_id: self.source_id }
    }
}
