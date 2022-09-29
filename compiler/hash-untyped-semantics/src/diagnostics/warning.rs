//! Hash AST semantic analysis warning diagnostic definitions.

use hash_ast::ast::{AstNodeId, AstNodeRef};
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::{identifier::Identifier, location::SourceLocation, SourceId};

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
    /// When an expression is in a position that will have no effect.
    UselessExpression,

    /// If a directive is specified that is not known to the compiler, this
    /// is currently a warning but it will become a hard error when directives
    /// are also subject to standard scoping rules.
    UnknownDirective { name: Identifier },
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
            AnalysisWarningKind::UnknownDirective { name } => {
                builder
                    .with_message(format!("`{name}` is not a known directive"))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        warning.location,
                        "",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "unknown directives are currently 'invisible' to the compiler and are treated as if they were just the inner expression. However, in the future this will become a hard error.",
                    )));
            }
        }

        builder.build()
    }
}
