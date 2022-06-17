//! Hash AST semantic passes error definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors.
use std::fmt::Display;

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
    pub(crate) fn new(kind: AnalysisErrorKind, location: SourceLocation) -> Self {
        Self { kind, location }
    }
}

/// The kind of [AnalyserError] that can occur.
pub(crate) enum AnalysisErrorKind {
    /// When a `break` expression is found outside of a loop.
    UsingBreakOutsideLoop,
    /// When a `continue` expression is found outside of a loop.
    UsingContinueOutsideLoop,
    /// When multiple spread patterns `...` are present within a list pattern
    MultipleSpreadPatterns {
        /// Where the use of the pattern originated from
        origin: PatternOrigin,
    },
    /// When a spread pattern is used within a parent pattern that does not allow them to be used.
    IllegalSpreadPatternUse {
        /// Where the use of the pattern originated from
        origin: PatternOrigin,
    },
    AmbiguousPatternFieldOrder {
        origin: PatternOrigin,
    },
}

/// Denotes where a pattern was used as in the parent of the pattern. This is useful
/// for propagating errors upwards by signalling what is the current parent of the
/// pattern. This only contains patterns that can be compound (hold multiple children patterns).
#[derive(Clone, Copy, Debug)]
pub(crate) enum PatternOrigin {
    Tuple,
    NamedField,
    Constructor,
    List,
    Namespace,
}

impl PatternOrigin {
    /// Convert the [PatternOrigin] into a string which can be used for displaying
    /// within error messages.
    fn to_str(self) -> &'static str {
        match self {
            PatternOrigin::Tuple => "tuple",
            PatternOrigin::NamedField => "named field",
            PatternOrigin::Constructor => "constructor",
            PatternOrigin::List => "list",
            PatternOrigin::Namespace => "namespace",
        }
    }
}

impl Display for PatternOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl From<AnalysisError> for Report {
    fn from(err: AnalysisError) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match err.kind {
            AnalysisErrorKind::UsingBreakOutsideLoop => {
                builder.with_error_code(HashErrorCode::UsingBreakOutsideLoop);

                builder
                    .with_message("You cannot use a `break` clause outside of a loop")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::UsingContinueOutsideLoop => {
                builder.with_error_code(HashErrorCode::UsingContinueOutsideLoop);

                builder
                    .with_message("You cannot use a `continue` clause outside of a loop")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::MultipleSpreadPatterns { origin } => {
                builder
                    .with_message(format!(
                        "Spread patterns `...` can only be used once in a {} pattern",
                        origin
                    ))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::IllegalSpreadPatternUse { origin } => {
                builder
                    .with_message(format!(
                        "Spread patterns `...` cannot be used in a {} pattern",
                        origin
                    ))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::AmbiguousPatternFieldOrder { origin } => {
                builder.with_message(format!("Ambiguous field order in `{}` pattern", origin));

                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "Un-named fields cannot appear after named fields",
                )));
            }
        };

        builder.build()
    }
}
