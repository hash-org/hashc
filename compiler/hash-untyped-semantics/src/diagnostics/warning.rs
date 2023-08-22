//! Hash AST semantic analysis warning diagnostic definitions.

use hash_ast::ast::{AstNodeId, AstNodeRef};
use hash_reporting::{
    report::{ReportCodeBlock, ReportElement, ReportNote, ReportNoteKind},
    reporter::{Reporter, Reports},
};
use hash_source::location::Span;

/// A [AnalysisWarning] is warning that can occur during the semantic pass
pub struct AnalysisWarning {
    /// The kind of warning
    kind: AnalysisWarningKind,

    /// Where the warning occurred
    location: Span,

    /// The associated [AstNodeRef<T>] with this error, which is used
    /// to sort the order that errors are emitted.
    id: AstNodeId,
}

impl AnalysisWarning {
    /// Create a new [AnalysisWarning] from a passed kind and [Span].
    pub(crate) fn new<T>(kind: AnalysisWarningKind, node: AstNodeRef<T>) -> Self {
        Self { kind, location: node.span(), id: node.id() }
    }

    /// Get the associated [AstNodeId] with this [AnalysisWarning].
    pub(crate) fn id(&self) -> AstNodeId {
        self.id
    }
}

/// The kind of [AnalysisWarning] that can occur.
pub(crate) enum AnalysisWarningKind {
    /// When an expression is in a position that will have no effect.
    UselessExpression,
}

impl From<AnalysisWarning> for Reports {
    fn from(warn: AnalysisWarning) -> Self {
        let mut reporter = Reporter::new();
        let warning = reporter.warning();

        match warn.kind {
            AnalysisWarningKind::UselessExpression => {
                warning
                    .title("this expression is useless")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        warn.location,
                        "here",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "A constant expression in a body block that has no side-effects is redundant",
                    )));
            } /* AnalysisWarningKind::UnknownDirective { name } => {
               *     warning
               *         .title(format!("`{name}` is not a known directive"))
               *         .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
               *             warn.location,
               *             "",
               *         )))
               *         .add_element(ReportElement::Note(ReportNote::new(
               *             ReportNoteKind::Note,
               *             "unknown directives are currently 'invisible' to the compiler and
               * are treated as if they were just the inner expression. However, in the future
               * this will become a hard error.",         )));
               * } */
        }

        reporter.into_reports()
    }
}
