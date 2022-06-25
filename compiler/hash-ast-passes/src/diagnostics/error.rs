//! Hash AST semantic analysis error diagnostic definitions.

use hash_ast::ast::Visibility;
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::location::SourceLocation;

use super::{BlockOrigin, PatternOrigin};

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

/// The kind of [AnalysisError] that can occur.
pub(crate) enum AnalysisErrorKind {
    /// When a `break` expression is found outside of a loop.
    UsingBreakOutsideLoop,
    /// When a `continue` expression is found outside of a loop.
    UsingContinueOutsideLoop,
    /// When a `return` statement is found outside of a function or in scope
    /// that doesn't relate to the function.
    UsingReturnOutsideOfFunction,
    /// When there is a non-declarative expression in either the root scope
    /// (module) or in a `impl` / `mod` block.
    NonDeclarativeExpression { origin: BlockOrigin },
    /// When multiple spread patterns `...` are present within a list pattern
    MultipleSpreadPatterns {
        /// Where the use of the pattern originated from
        origin: PatternOrigin,
    },
    /// When a spread pattern is used within a parent pattern that does not
    /// allow them to be used.
    IllegalSpreadPatternUse {
        /// Where the use of the pattern originated from
        origin: PatternOrigin,
    },
    /// When compound patterns such as constructors and tuples have named fields
    /// before un-named fields.
    AmbiguousPatternFieldOrder { origin: PatternOrigin },
    /// When a top-level declaration features a pattern that has a binding which
    /// is declared to be mutable.
    IllegalBindingMutability,
    /// When bindings declare themselves to be `pub` or `priv` within
    /// non-constant blocks like function bodies.
    IllegalBindingVisibilityModifier { modifier: Visibility, origin: BlockOrigin },
}

impl From<AnalysisError> for Report {
    fn from(err: AnalysisError) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match err.kind {
            AnalysisErrorKind::UsingBreakOutsideLoop => {
                builder.with_error_code(HashErrorCode::UsingBreakOutsideLoop);

                builder.with_message("use of a `break` clause outside of a loop").add_element(
                    ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")),
                );
            }
            AnalysisErrorKind::UsingContinueOutsideLoop => {
                builder.with_error_code(HashErrorCode::UsingContinueOutsideLoop);

                builder.with_message("use of a `continue` clause outside of a loop").add_element(
                    ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")),
                );
            }
            AnalysisErrorKind::UsingReturnOutsideOfFunction => {
                builder.with_error_code(HashErrorCode::UsingReturnOutsideFunction);

                builder
                    .with_message("use of a `return` expression outside of a function")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::MultipleSpreadPatterns { origin } => {
                builder
                    .with_message(format!(
                        "spread patterns `...` can only be used once in a {} pattern",
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
                        "spread patterns `...` cannot be used in a {} pattern",
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
                    "un-named fields cannot appear after named fields",
                )));
            }
            AnalysisErrorKind::NonDeclarativeExpression { origin } => {
                builder.with_message(format!(
                    "non-declarative expressions are not allowed in `{}` pattern",
                    origin
                ));

                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "not allowed here",
                )));
            }
            AnalysisErrorKind::IllegalBindingMutability => {
                builder.with_message("top-level declaration cannot be mutable");

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        "consider removing `mut` from the declaration",
                    )));
            }
            AnalysisErrorKind::IllegalBindingVisibilityModifier { modifier, origin } => {
                builder.with_message(format!(
                    "declarations in {} blocks cannot have visibility modifiers",
                    origin
                ));

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        format!("{} blocks cannot have `{}` explicit visibility", origin, modifier),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        format!(
                            "declarations in `{}` blocks by default have private visibility.",
                            origin
                        ),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        "consider removing the visibility modifier",
                    )));
            }
        };

        builder.build()
    }
}
