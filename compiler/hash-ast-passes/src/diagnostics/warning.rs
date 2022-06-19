//! Hash AST semantic analysis warning diagnostic definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors.

use hash_reporting::reporting::{
    Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind,
};
use hash_source::location::SourceLocation;

/// A [AnalysisWarning] is warning that can occur during the semantic pass
pub struct AnalysisWarning {
    /// The kind of warning
    kind: AnalysisWarningKind,

    /// Where the warning occurred
    location: SourceLocation,
}

impl AnalysisWarning {
    /// Create a new [AnalysisWarning] from a passed kind and [SourceLocation].
    pub(crate) fn new(kind: AnalysisWarningKind, location: SourceLocation) -> Self {
        Self { kind, location }
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
