//! Hash AST semantic passes error definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors.
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::reporting::{
    Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind,
};
use hash_source::location::SourceLocation;

/// An error that can occur during the semantic pass
pub struct AnalysisError {
    /// The kind of error
    kind: AnalysisErrorKind,

    /// Where the error occurred
    location: SourceLocation,
}

impl AnalysisError {
    /// Create a new [AnalysisError] from a passed kind and [SourceLocation].
    pub fn new(kind: AnalysisErrorKind, location: SourceLocation) -> Self {
        Self { kind, location }
    }
}

/// The kind of [AnalyserError] that can occur.
pub enum AnalysisErrorKind {
    /// When a `break` expression is found outside of a loop.
    UsingBreakOutsideLoop,
    /// When a `continue` expression is found outside of a loop.
    UsingContinueOutsideLoop,
}

impl From<AnalysisError> for Report {
    fn from(err: AnalysisError) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match err.kind {
            AnalysisErrorKind::UsingBreakOutsideLoop => {
                builder.with_message("You cannot use a `break` clause outside of a loop.");
                builder.with_error_code(HashErrorCode::UsingBreakOutsideLoop);
            }
            AnalysisErrorKind::UsingContinueOutsideLoop => {
                builder.with_message("You cannot use a `continue` clause outside of a loop.");
                builder.with_error_code(HashErrorCode::UsingContinueOutsideLoop);
            }
        };

        // @@TODO: this might be too generic
        builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
            err.location,
            "here",
        )));

        builder.build()
    }
}
