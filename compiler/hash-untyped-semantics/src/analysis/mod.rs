//! Hash semantic analyser definitions. This file holds the [SemanticAnalyser]
//! definition with some shared functions to append diagnostics to the analyser.

mod block;
pub(crate) mod params;

use hash_ast::{ast::AstNodeRef, origin::BlockOrigin};
use hash_reporting::diagnostic::HasDiagnosticsMut;
use hash_utils::crossbeam_channel::Sender;

use crate::diagnostics::{
    AnalyserDiagnostics, AnalysisDiagnostic,
    error::{AnalysisError, AnalysisErrorKind},
    warning::{AnalysisWarning, AnalysisWarningKind},
};

pub struct SemanticAnalyser {
    /// Whether the current visitor is within a loop construct.
    pub(crate) is_in_loop: bool,

    /// Whether the current visitor is within a function definition.
    pub(crate) is_in_fn: bool,

    /// Whether the analyser is currently checking a literal pattern
    pub(crate) is_in_lit_pat: bool,

    /// The current scope of the traversal, representing which block the
    /// analyser is walking.
    pub(crate) current_block: BlockOrigin,

    /// [SemanticAnalyser] diagnostics store
    pub(crate) diagnostics: AnalyserDiagnostics,
}

impl Default for SemanticAnalyser {
    fn default() -> Self {
        Self::new()
    }
}

impl SemanticAnalyser {
    /// Create a new semantic analyser
    pub fn new() -> Self {
        Self {
            is_in_loop: false,
            is_in_fn: false,
            is_in_lit_pat: false,
            diagnostics: AnalyserDiagnostics::default(),
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

    /// Append an error to [AnalyserDiagnostics]
    pub(crate) fn append_error<T>(&mut self, error: AnalysisErrorKind, node: AstNodeRef<T>) {
        self.add_error(AnalysisError::new(error, node))
    }

    /// Append an warning to [AnalyserDiagnostics]
    pub(crate) fn append_warning<T>(&mut self, warning: AnalysisWarningKind, node: AstNodeRef<T>) {
        self.add_warning(AnalysisWarning::new(warning, node))
    }

    /// Given a [Sender], send all of the generated warnings and messaged into
    /// the sender.
    pub(crate) fn emit_diagnostics_to(self, sender: &Sender<AnalysisDiagnostic>) {
        self.diagnostics.store.errors.into_iter().for_each(|t| sender.send(t.into()).unwrap());
        self.diagnostics.store.warnings.into_iter().for_each(|t| sender.send(t.into()).unwrap());
    }
}
