//! Reporting for typechecking diagnostics.
//!
//! This formats the diagnostics in `definitions.rs` nicely
//! through the compiler's reporting system (`hash-reporting`).
use std::fmt;

use hash_reporting::{
    hash_error_codes::error_codes::HashErrorCode,
    reporter::{Reporter, Reports},
};
use hash_storage::store::SequenceStoreKey;
use hash_tir::tir::{HasAstNodeId, NodeId, NodeOrigin, ParamError, SomeParamsOrArgsId};

use super::definitions::WrongTermKind;
use crate::diagnostics::definitions::TcError;

/// Unit struct that contains the typechecking reporting implementation.
pub struct TcReporter;

impl fmt::Display for TcReporter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reports = Self::format_error(&TcError::Signal);
        write!(f, "{}", Reporter::from_reports(reports))
    }
}

impl TcReporter {
    /// Format the error nicely and return it as a set of reports.
    pub fn format_error(error: &TcError) -> Reports {
        let mut builder = Reporter::new();
        Self::add_to_reporter(error, &mut builder);
        builder.into_reports()
    }

    /// Format the error nicely and add it to the given reporter.
    pub fn add_to_reporter(error: &TcError, reporter: &mut Reporter) {
        match error {
            TcError::Signal => {}
            TcError::Blocked(location) => {
                let error = reporter.error().title("blocked while typechecking".to_string());

                if let Some(location) = location.span() {
                    error.add_span(location);
                }
            }
            TcError::NeedMoreTypeAnnotationsToInfer { atom } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedType)
                    .title(format!("cannot infer the type of this term: `{}`", *atom));

                if let Some(location) = atom.span() {
                    error
                        .add_span(location)
                        .add_help("consider adding more type annotations to this expression");
                }
            }
            TcError::Compound { errors } => {
                for error in errors {
                    Self::add_to_reporter(error, reporter);
                }
            }
            TcError::WrongArgLength { params_id, args_id } => {
                let param_length = params_id.len();
                let arg_length = args_id.len();

                let error =
                    reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                        "mismatch in parameter length: expected {param_length} but got {arg_length}"
                    ));

                if let Some(location) = params_id.span() {
                    error
                        .add_span(location)
                        .add_info(format!("expected {param_length} parameters here"));
                }

                if let Some(location) = {
                    let target = *args_id;
                    target.span()
                } {
                    error
                        .add_span(location)
                        .add_info(format!("got {arg_length} {} here", args_id.as_str()));
                }
            }
            TcError::CannotDeref { subject, actual_subject_ty } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::InvalidCallSubject)
                    .title("the subject of this dereference is not a reference");
                if let Some(location) = subject.span() {
                    error.add_labelled_span(
                        location,
                        format!(
                            "cannot use this as a subject of a dereference operation. It is of type `{}` which is not a reference type.",
                            *actual_subject_ty
                        )
                    );
                }
            }
            TcError::MismatchingTypes { expected, actual } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::TypeMismatch)
                    .title(format!("expected type `{}` but got `{}`", *expected, *actual,));
                if let NodeOrigin::InferredFrom(location) = actual.origin() {
                    error.add_labelled_span(
                        location.span(),
                        format!("type `{}` inferred from here", *actual),
                    );
                }
                if let Some(location) = expected.span() {
                    error.add_labelled_span(location, format!("this expects type `{}`", *expected));
                }
                if let Some(location) = actual.span() {
                    error.add_labelled_span(location, format!("this is of type `{}`", *actual));
                }
            }
            TcError::UndecidableEquality { a, b } => {
                let error = reporter.error().code(HashErrorCode::TypeMismatch).title(format!(
                    "cannot determine if expressions `{}` and `{}` are equal",
                    *a, *b,
                ));
                if let Some(location) = a.span() {
                    error.add_labelled_span(
                        location,
                        format!(
                            "`{}` from here", //@@Todo: flag for if inferred or declared
                            (*a)
                        ),
                    );
                }
                if let Some(location) = b.span() {
                    error.add_labelled_span(location, format!("`{}` from here", *b));
                }
            }
            TcError::ParamMatch(err) => {
                ParamError::add_to_reporter(err, reporter);
            }
            TcError::LitParseError(err) => {
                err.add_to_reporter(reporter);
            }
            TcError::WrongTerm { term, inferred_term_ty, kind } => {
                let kind_name = match kind {
                    WrongTermKind::NotAFunction => "function".to_string(),
                    WrongTermKind::NotARecord => "record".to_string(),
                    WrongTermKind::NotAnArray => "array".to_string(),
                    WrongTermKind::NotOfType { correct_ty } => {
                        format!("value of type `{}`", *correct_ty)
                    }
                };

                let error =
                    reporter.error().code(HashErrorCode::InvalidCallSubject).title(format!(
                        "expected a {}, but got type `{}` instead",
                        kind_name, *inferred_term_ty
                    ));

                if let Some(location) = term.span() {
                    error.add_labelled_span(
                        location,
                        format!("expected a {kind_name}, but got this value instead"),
                    );
                }

                if let Some(location) = inferred_term_ty.span() {
                    error.add_labelled_span(
                        location,
                        format!("this value has type `{}`", *inferred_term_ty),
                    );
                }
            }
            TcError::PropertyNotFound { term, term_ty, property } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::InvalidPropertyAccess)
                    .title(format!("property `{}` not found on type `{}`", *property, *term_ty));
                if let Some(location) = term.span() {
                    error.add_labelled_span(
                        location,
                        format!(
                            "term has type `{}`. Property `{}` is not present on this type",
                            *term_ty, *property,
                        ),
                    );
                }
            }
            TcError::WrongParamLength { given_params_id, annotation_params_id } => {
                let error =
                    reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                        "wrong number of parameters. Expected {} but got {}",
                        annotation_params_id.len(),
                        given_params_id.len()
                    ));
                if let Some(location) = given_params_id.span() {
                    error.add_labelled_span(
                        location,
                        format!("got {} parameters here", given_params_id.len(),),
                    );
                }
                if let Some(location) = annotation_params_id.span() {
                    error.add_labelled_span(
                        location,
                        format!("expected {} parameters from here", annotation_params_id.len(),),
                    );
                }
            }
            TcError::WrongCallKind { site, expected_implicit, actual_implicit } => {
                let get_call_kind = |implicit: &bool| {
                    if *implicit { "implicit (`<...>`)" } else { "explicit (`(...)`)" }
                };
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnsupportedImplicitFnApplication)
                    .title(format!(
                        "expected an {} call but got an {} call",
                        get_call_kind(expected_implicit),
                        get_call_kind(actual_implicit)
                    ));
                if let Some(location) = site.span() {
                    error.add_labelled_span(location, "unexpected call kind at this call site");
                }
            }
            TcError::Intrinsic(msg) => {
                let _error = reporter.error().code(HashErrorCode::TypeMismatch).title(msg);
            }
            TcError::MismatchingArrayLengths { expected_len, got_len } => {
                let error =
                    reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                        "expected array of length {} but got array of length {}",
                        *expected_len, *got_len
                    ));
                if let Some(location) = expected_len.span() {
                    error.add_labelled_span(location, "expected array length");
                }
                if let Some(location) = got_len.span() {
                    error.add_labelled_span(location, "got array length");
                }
            }
            TcError::MismatchingPats { a, b } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::TypeMismatch)
                    .title(format!("expected pattern `{}`, but got pattern `{}`", *a, *b));
                if let Some(location) = a.span() {
                    error.add_labelled_span(location, "expected pattern");
                }
                if let Some(location) = b.span() {
                    error.add_labelled_span(location, "got pattern");
                }
            }
            TcError::MismatchingFns { a, b } => {
                let error = reporter.error().code(HashErrorCode::TypeMismatch).title(format!(
                    "expected function `{}`, but got function `{}`. Functions are only equal if they refer to the same function definition",
                    *a,
                    *b
                ));
                if let Some(location) = a.span() {
                    error.add_labelled_span(location, "expected function");
                }
                if let Some(location) = b.span() {
                    error.add_labelled_span(location, "got function");
                }
            }
            TcError::DifferentParamOrArgLengths { a, b } => {
                let name_of_args = match a {
                    SomeParamsOrArgsId::Params(_) => "parameters",
                    SomeParamsOrArgsId::PatArgs(_) => "pattern arguments",
                    SomeParamsOrArgsId::Args(_) => "arguments",
                };
                let error = reporter.error().code(HashErrorCode::TypeMismatch).title(format!(
                    "expected `{}` {name_of_args} but got `{}` {name_of_args} ",
                    a.len(),
                    b.len()
                ));
                if let Some(location) = {
                    let target = *a;
                    target.span()
                } {
                    error.add_labelled_span(
                        location,
                        format!("expected {} {name_of_args} here", a.len()),
                    );
                }
                if let Some(location) = {
                    let target = *b;
                    target.span()
                } {
                    error.add_labelled_span(
                        location,
                        format!("got {} {name_of_args} here", b.len()),
                    );
                }
            }
            TcError::NeedMoreTypeAnnotationsToUnify { src, target } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::TypeMismatch)
                    .title(format!("cannot unify `{}` with `{}`", *src, *target));
                if let Some(location) = src.span() {
                    error.add_labelled_span(location, "cannot unify this type");
                }
                if let Some(location) = target.span() {
                    error.add_labelled_span(location, "with this type");
                }
            }
            TcError::TryingToReferenceLocalsInType { ty } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::DisallowedType)
                    .title(format!("cannot use locals from this block in type `{}`", *ty));
                if let Some(location) = ty.span() {
                    error.add_labelled_span(location, "type containing locals");
                }
            }
        }
    }
}
