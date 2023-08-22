//! Hash AST semantic analysis error diagnostic definitions.

use hash_ast::{
    ast::{AstNodeId, AstNodeRef, ParamOrigin, RangeEnd, Visibility},
    origin::BlockOrigin,
};
use hash_reporting::{
    hash_error_codes::error_codes::HashErrorCode,
    report::{ReportCodeBlock, ReportElement, ReportNote, ReportNoteKind},
    reporter::{Reporter, Reports},
};
use hash_source::{identifier::Identifier, location::Span};

// use super::directives::DirectiveArgument;
use crate::analysis::params::FieldNamingExpectation;

/// An error that can occur during the semantic pass
pub struct AnalysisError {
    /// The kind of error
    kind: AnalysisErrorKind,

    /// Where the error occurred
    location: Span,

    /// The associated [AstNodeRef<T>] with this error, which is used
    /// to sort the order that errors are emitted.
    id: AstNodeId,
}

impl AnalysisError {
    /// Create a new [AnalysisError] from a passed kind and [Span].
    pub(crate) fn new<T>(kind: AnalysisErrorKind, node: AstNodeRef<T>) -> Self {
        Self { kind, location: node.span(), id: node.id() }
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

    /// When a pattern is used within a particular context that is not allowed
    ///
    /// Currently, this is only used to notify that `float` patterns aren't
    /// allowed in pattern positions. Later this will change as float
    /// patterns should be allowed within range patterns.
    DisallowedFloatPat,

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
    // DisallowedDirective { name: Identifier, module_kind: Option<ModuleKind> },

    /// When a directive is expecting a particular expression, but received an
    /// unexpected kind...
    // InvalidDirectiveArgument {
    //     /// The name of the directive.
    //     name: Identifier,

    //     /// A collection of allowed directive arguments, e.g. `struct` or `enum`
    //     /// definition.
    //     expected: DirectiveArgument,

    //     /// The received argument.
    //     received: DirectiveArgument,

    //     /// Any additional information about this particular invocation.
    //     notes: Vec<String>,
    // },

    /// When a directive is used within an un-expected scope,
    InvalidDirectiveScope { name: Identifier, expected: BlockOrigin, received: BlockOrigin },

    /// When fields of a `struct` or `enum` use inconsistent naming
    InconsistentFieldNaming {
        /// Whether the name is expected to be named or not.
        naming_expectation: FieldNamingExpectation,

        /// The origin of where the parameter came from.
        origin: ParamOrigin,
    },

    /// When a range ending is specified as exclusive, but doesn't specify a
    /// terminating value.
    ExclusiveRangeWithNoEnding,
}

impl From<AnalysisError> for Reports {
    fn from(err: AnalysisError) -> Self {
        let mut reporter = Reporter::new();
        let error = reporter.error();

        match err.kind {
            AnalysisErrorKind::UsingBreakOutsideLoop => {
                error.code(HashErrorCode::UsingBreakOutsideLoop);

                error.title("use of a `break` clause outside of a loop").add_element(
                    ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")),
                );
            }
            AnalysisErrorKind::UsingContinueOutsideLoop => {
                error.code(HashErrorCode::UsingContinueOutsideLoop);

                error.title("use of a `continue` clause outside of a loop").add_element(
                    ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")),
                );
            }
            AnalysisErrorKind::UsingReturnOutsideOfFn => {
                error.code(HashErrorCode::UsingReturnOutsideFn);

                error.title("use of a `return` expression outside of a function").add_element(
                    ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")),
                );
            }
            AnalysisErrorKind::NonDeclarativeExpression { origin } => {
                error.title(format!(
                    "non-declarative expressions are not allowed in `{origin}` pattern"
                ));

                error.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "not allowed here",
                )));
            }
            AnalysisErrorKind::IllegalBindingMutability => {
                error.title("top-level declaration cannot be mutable");

                error
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
                error.title(format!(
                    "declarations in {origin} blocks cannot have visibility modifiers"
                ));

                error
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
                error.title(format!(
                    "`{}` {} does not have enough information",
                    origin,
                    origin.field_name()
                ));

                error
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
            // AnalysisErrorKind::DisallowedDirective { name, module_kind } => {
            //     let origin = match module_kind {
            //         Some(_) => "this module",
            //         None => "an interactive",
            //     };

            //     error
            //         .title(format!("the `{name}` directive is disallowed within {origin}
            // context"));

            //     // Show the location where the directive is being used...
            //     error.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
            //         err.location,
            //         format!("`{name}` cannot be used within {origin} context"),
            //     )));
            // }
            AnalysisErrorKind::InvalidDirectiveScope { name, expected, received } => {
                error.title(format!("the `{name}` directive is must be within a {expected} block"));

                // Show the location where the directive is being used...
                error.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    format!("`{name}` cannot be used within {received} block"),
                )));
            }
            // AnalysisErrorKind::InvalidDirectiveArgument { name, expected, received, notes } => {
            //     error.title(format!("the `{name}` directive expects {expected} as an argument"));

            //     // Show the location where the directive is being used...
            //     error.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
            //         err.location,
            //         format!("{received} cannot be given to the `{name}` directive"),
            //     )));

            //     // Add any notes that were given with this error
            //     for note in notes {
            //         error.add_note(note);
            //     }
            // }
            AnalysisErrorKind::DisallowedFloatPat => {
                error.title("float literals are disallowed within a pattern position");

                error
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "float-like literals are disallowed within patterns because performing comparisons is not possible",
                    )));
            }
            AnalysisErrorKind::InconsistentFieldNaming { naming_expectation, origin } => {
                error.title(format!("mismatching naming convention of fields within a {origin}"));

                error
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
                error.title("`self` parameter is only allowed in associated functions");

                error.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    err.location,
                    "`self` not semantically valid here",
                )));
            }
            AnalysisErrorKind::ExclusiveRangeWithNoEnding => {
                error.title(format!("incomplete range ending, ranges that specify a `{}` must specify an ending range operand", RangeEnd::Excluded))
                .add_labelled_span(err.location, "add an ending range operand here");
            }
        };

        reporter.into_reports()
    }
}
