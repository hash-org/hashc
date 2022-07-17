//! Hash AST semantic analysis error diagnostic definitions.

use hash_ast::ast::Visibility;
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::{identifier::Identifier, location::SourceLocation, ModuleKind};

use super::{
    directives::DirectiveArgument,
    origins::{BlockOrigin, FieldOrigin, PatternOrigin},
};

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
    /// When a pattern is used within a particular context that is not allowed
    ///
    /// Currently, this is only used to notify that `float` patterns aren't
    /// allowed in pattern positions. Later this will change as float
    /// patterns should be allowed within range patterns.
    DisallowedFloatPattern,
    /// When compound patterns such as constructors and tuples have named fields
    /// before un-named fields.
    AmbiguousPatternFieldOrder { origin: PatternOrigin },
    /// When a top-level declaration features a pattern that has a binding which
    /// is declared to be mutable.
    IllegalBindingMutability,
    /// When bindings declare themselves to be `pub` or `priv` within
    /// non-constant blocks like function bodies.
    IllegalBindingVisibilityModifier { modifier: Visibility, origin: BlockOrigin },
    /// When a field within a struct, tuple or other form is missing both a type
    /// annotation and a default value, which means that there is not enough
    /// information at later stages to deduce the type of the field.
    InsufficientTypeAnnotations { origin: FieldOrigin },
    /// When a directive is not allowed in the current module or context
    DisallowedDirective { name: Identifier, module_kind: Option<ModuleKind> },
    /// When a directive is expecting a particular expression, but received an
    /// unexpected kind...
    InvalidDirectiveArgument {
        name: Identifier,
        expected: DirectiveArgument,
        given: DirectiveArgument,
    },
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
                builder
                    .with_error_code(HashErrorCode::AmbiguousFieldOrder)
                    .with_message(format!("Ambiguous field order in `{}` pattern", origin));

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
            AnalysisErrorKind::InsufficientTypeAnnotations { origin } => {
                builder
                    .with_message(format!("`{}` field does not have enough information", origin));

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        format!(
                            "this {} field is missing a type annotation and a default value",
                            origin
                        ),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        format!("consider giving this {} field a type annotation", origin),
                    )));
            }
            AnalysisErrorKind::DisallowedDirective { name, module_kind } => {
                let origin = match module_kind {
                    Some(_) => "this module",
                    None => "an interactive",
                };

                builder.with_message(format!(
                    "the `{}` directive is disallowed within {} context",
                    name, origin
                ));

                // Show the location where the directive is being used...
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("`{}` cannot be used within {} context", name, origin),
                )));
            }
            AnalysisErrorKind::InvalidDirectiveArgument { name, expected, given } => {
                builder.with_message(format!(
                    "the `{}` directive expects a {} as an argument",
                    name, expected
                ));

                // Show the location where the directive is being used...
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("a {} cannot be given to the `{}` directive", given, name),
                )));
            }
            AnalysisErrorKind::DisallowedFloatPattern => {
                builder.with_message("float literals are disallowed within a pattern position");

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "float-like literals are disallowed within patterns because performing comparisons is not possible",
                    )));
            }
        };

        builder.build()
    }
}
