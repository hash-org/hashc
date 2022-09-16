//! Hash AST semantic analysis warning diagnostic definitions.

use hash_ast::ast::{AstNodeId, AstNodeRef};
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::{location::SourceLocation, SourceId};

/// A [AnalysisWarning] is warning that can occur during the semantic pass
pub struct AnalysisWarning {
    /// The kind of warning
    kind: AnalysisWarningKind,

    /// Where the warning occurred
    location: SourceLocation,

    /// The associated [AstNodeRef<T>] with this error, which is used
    /// to sort the order that errors are emitted.
    id: AstNodeId,
}

impl AnalysisWarning {
    /// Create a new [AnalysisWarning] from a passed kind and [SourceLocation].
    pub(crate) fn new<T>(kind: AnalysisWarningKind, node: AstNodeRef<T>, id: SourceId) -> Self {
        Self { kind, location: SourceLocation { span: node.span(), id }, id: node.id() }
    }

    /// Get the associated [AstNodeId] with this [AnalysisWarning].
    pub(crate) fn id(&self) -> AstNodeId {
        self.id
    }
}

/// The kind of [AnalysisWarning] that can occur.
pub(crate) enum AnalysisWarningKind {
    UselessExpression,
}

impl From<AnalysisWarning> for Report {
    fn from(warning: AnalysisWarning) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Warning);

        match warning.kind {
            AnalysisWarningKind::UselessExpression => {
                builder
                    .with_message("this expression is useless")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        warning.location,
                        "here",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "A constant expression in a body block that has no side-effects is redundant",
                    )));
            }
        }

        builder.build()
    }
}
