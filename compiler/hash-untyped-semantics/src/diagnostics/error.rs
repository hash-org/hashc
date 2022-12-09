//! Hash AST semantic analysis error diagnostic definitions.

use hash_ast::{
    ast::{AstNodeId, AstNodeRef, ParamOrigin, Visibility},
    origin::BlockOrigin,
};
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::{identifier::Identifier, location::SourceLocation, ModuleKind, SourceId};

use super::{directives::DirectiveArgument, origins::PatOrigin};
use crate::analysis::params::FieldNamingExpectation;

/// An error that can occur during the semantic pass
pub struct AnalysisError {
    /// The kind of error
    kind: AnalysisErrorKind,

    /// Where the error occurred
    location: SourceLocation,

    /// The associated [AstNodeRef<T>] with this error, which is used
    /// to sort the order that errors are emitted.
    id: AstNodeId,
}

impl AnalysisError {
    /// Create a new [AnalysisError] from a passed kind and [SourceLocation].
    pub(crate) fn new<T>(kind: AnalysisErrorKind, node: AstNodeRef<T>, id: SourceId) -> Self {
        Self { kind, location: SourceLocation { span: node.span(), id }, id: node.id() }
    }

    /// Get the associated [AstNodeId] with this [AnalysisError].
    pub(crate) fn id(&self) -> AstNodeId {
        self.id
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
    UsingReturnOutsideOfFn,
    /// When there is a non-declarative expression in either the root scope
    /// (module) or in a `impl` / `mod` block.
    NonDeclarativeExpression { origin: BlockOrigin },
    /// When multiple spread patterns `...` are present within a list pattern
    MultipleSpreadPats {
        /// Where the use of the pattern originated from
        origin: PatOrigin,
    },
    /// When a spread pattern is used within a parent pattern that does not
    /// allow them to be used.
    IllegalSpreadPatUse {
        /// Where the use of the pattern originated from
        origin: PatOrigin,
    },
    /// When a pattern is used within a particular context that is not allowed
    ///
    /// Currently, this is only used to notify that `float` patterns aren't
    /// allowed in pattern positions. Later this will change as float
    /// patterns should be allowed within range patterns.
    DisallowedFloatPat,
    /// When compound patterns such as constructors and tuples have named fields
    /// before un-named fields.
    AmbiguousPatFieldOrder { origin: PatOrigin },
    /// When a top-level declaration features a pattern that has a binding which
    /// is declared to be mutable.
    IllegalBindingMutability,
    /// When bindings declare themselves to be `pub` or `priv` within
    /// non-constant blocks like function bodies.
    IllegalBindingVisibilityModifier { modifier: Visibility, origin: BlockOrigin },
    /// When a field within a struct, tuple or other form is missing both a type
    /// annotation and a default value, which means that there is not enough
    /// information at later stages to deduce the type of the field.
    InsufficientTypeAnnotations { origin: ParamOrigin },

    /// Using `self` within free-standing functions
    SelfInFreeStandingFn,

    /// When a directive is not allowed in the current module or context
    DisallowedDirective { name: Identifier, module_kind: Option<ModuleKind> },
    /// When a directive is expecting a particular expression, but received an
    /// unexpected kind...
    InvalidDirectiveArgument {
        name: Identifier,
        expected: DirectiveArgument,
        received: DirectiveArgument,
    },
    /// When a directive is used within an un-expected scope,
    InvalidDirectiveScope { name: Identifier, expected: BlockOrigin, received: BlockOrigin },
    /// When fields of a `struct` or `enum` use inconsistent naming
    InconsistentFieldNaming {
        /// Whether the name is expected to be named or not.
        naming_expectation: FieldNamingExpectation,

        /// The origin of where the parameter came from.
        origin: ParamOrigin,
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
            AnalysisErrorKind::UsingReturnOutsideOfFn => {
                builder.with_error_code(HashErrorCode::UsingReturnOutsideFn);

                builder
                    .with_message("use of a `return` expression outside of a function")
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::MultipleSpreadPats { origin } => {
                builder
                    .with_message(format!(
                        "spread patterns `...` can only be used once in a {origin} pattern"
                    ))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::IllegalSpreadPatUse { origin } => {
                builder
                    .with_message(format!(
                        "spread patterns `...` cannot be used in a {origin} pattern"
                    ))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        "here",
                    )));
            }
            AnalysisErrorKind::AmbiguousPatFieldOrder { origin } => {
                builder
                    .with_error_code(HashErrorCode::AmbiguousFieldOrder)
                    .with_message(format!("ambiguous field order in `{origin}` pattern"));

                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "un-named fields cannot appear after named fields",
                )));
            }
            AnalysisErrorKind::NonDeclarativeExpression { origin } => {
                builder.with_message(format!(
                    "non-declarative expressions are not allowed in `{origin}` pattern"
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
                    "declarations in {origin} blocks cannot have visibility modifiers"
                ));

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        format!("{origin} blocks cannot have `{modifier}` explicit visibility"),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        format!(
                            "declarations in `{origin}` blocks by default have private visibility."
                        ),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        "consider removing the visibility modifier",
                    )));
            }
            AnalysisErrorKind::InsufficientTypeAnnotations { origin } => {
                builder.with_message(format!(
                    "`{}` {} does not have enough information",
                    origin,
                    origin.field_name()
                ));

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        format!(
                            "this `{}` {} is missing both a type annotation and a default value",
                            origin,
                            origin.field_name()
                        ),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        format!("consider giving this {origin} field a type annotation"),
                    )));
            }
            AnalysisErrorKind::DisallowedDirective { name, module_kind } => {
                let origin = match module_kind {
                    Some(_) => "this module",
                    None => "an interactive",
                };

                builder.with_message(format!(
                    "the `{name}` directive is disallowed within {origin} context"
                ));

                // Show the location where the directive is being used...
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("`{name}` cannot be used within {origin} context"),
                )));
            }
            AnalysisErrorKind::InvalidDirectiveScope { name, expected, received } => {
                builder.with_message(format!(
                    "the `{name}` directive is must be within a {expected} block"
                ));

                // Show the location where the directive is being used...
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("`{name}` cannot be used within {received} block"),
                )));
            }
            AnalysisErrorKind::InvalidDirectiveArgument { name, expected, received: given } => {
                builder.with_message(format!(
                    "the `{name}` directive expects a {expected} as an argument"
                ));

                // Show the location where the directive is being used...
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("a {given} cannot be given to the `{name}` directive"),
                )));
            }
            AnalysisErrorKind::DisallowedFloatPat => {
                builder.with_message("float literals are disallowed within a pattern position");

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "float-like literals are disallowed within patterns because performing comparisons is not possible",
                    )));
            }
            AnalysisErrorKind::InconsistentFieldNaming { naming_expectation, origin } => {
                builder.with_message(format!(
                    "mismatching naming convention of fields within a {origin}"
                ));

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        err.location,
                        format!("this is expected to be a {naming_expectation} field"),
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        format!("fields of a {origin} should all be named or all un-named"),
                    )));
            }
            AnalysisErrorKind::SelfInFreeStandingFn => {
                builder.with_message("`self` parameter is only allowed in associated functions");

                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "`self` not semantically valid here",
                )));
            }
        };

        builder.build()
    }
}
