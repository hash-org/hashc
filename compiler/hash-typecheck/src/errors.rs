use std::{fmt, mem::take};

use derive_more::Constructor;
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    reporter::{Reporter, Reports},
    writer::ReportWriter,
};
use hash_source::location::SourceLocation;
use hash_tir::{
    impl_access_to_env,
    new::{
        defs::DefParamsId,
        environment::env::{AccessToEnv, Env},
        params::{ParamsId, SomeArgsId, SomeDefArgsId},
        terms::TermId,
        tys::TyId,
        utils::common::CommonUtils,
    },
};
use hash_utils::store::SequenceStoreKey;

/// Accumulates errors that occur during typechecking in a local scope.
///
/// This is used for error recovery, so that multiple errors can be reported
/// at once.
pub struct TcErrorState {
    pub errors: Vec<TcError>,
    pub has_blocked: bool,
}

impl TcErrorState {
    pub fn new() -> Self {
        Self { errors: vec![], has_blocked: false }
    }

    /// Add an error to the error state.
    pub fn add_error(&mut self, error: TcError) -> &TcError {
        if let TcError::Blocked = error {
            self.has_blocked = true;
        }
        self.errors.push(error);
        self.errors.last().unwrap()
    }

    /// Add an error to the error state if the given result is an error.
    pub fn try_or_add_error<F>(&mut self, f: TcResult<F>) -> Option<F> {
        match f {
            Ok(v) => Some(v),
            Err(e) => {
                self.add_error(e);
                None
            }
        }
    }

    /// Add a set of errors to the error state.
    pub fn add_errors(&mut self, errors: impl IntoIterator<Item = TcError>) {
        self.errors.extend(errors);
    }

    /// Whether the error state has any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Take the errors from the error state.
    pub fn take_errors(&mut self) -> Vec<TcError> {
        take(&mut self.errors)
    }
}

impl Default for TcErrorState {
    fn default() -> Self {
        Self::new()
    }
}

/// An error that occurs during typechecking.
#[derive(Clone, Debug)]

pub enum TcError {
    /// Blocked, cannot continue. This is used as a signal in the typechecker.
    Blocked,
    /// Signal to assert that there are other errors in the diagnostics store.
    Signal,
    /// A series of errors.
    Compound { errors: Vec<TcError> },
    /// An error exists, this is just a signal to stop typechecking. Signal,
    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },
    /// The given arguments do not match the length of the target parameters.
    WrongArgLength { params_id: ParamsId, args_id: SomeArgsId },
    /// The given definition arguments do not match the length of the target
    /// definition parameters.
    WrongDefArgLength { def_params_id: DefParamsId, def_args_id: SomeDefArgsId },
    /// Not a function.
    NotAFunction { fn_call: TermId, actual_subject_ty: TyId },
    /// Cannot deref the subject.
    CannotDeref { subject: TermId, actual_subject_ty: TyId },
    /// Types don't match
    MismatchingTypes { expected: TyId, actual: TyId },
    /// Undecidable equality between terms
    UndecidableEquality { a: TermId, b: TermId },
    /// Invalid range pattern literal
    InvalidRangePatternLiteral { location: SourceLocation },
}

pub type TcResult<T> = Result<T, TcError>;

#[derive(Constructor)]
pub struct TcErrorReporter<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(TcErrorReporter<'env>);

impl fmt::Display for TcErrorReporter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reports = self.format_error(&TcError::Signal);
        write!(f, "{}", ReportWriter::new(reports, self.source_map()))
    }
}

impl<'tc> TcErrorReporter<'tc> {
    /// Format the error nicely and return it as a set of reports.
    pub fn format_error(&self, error: &TcError) -> Reports {
        let mut builder = Reporter::new();
        self.add_to_reporter(error, &mut builder);
        builder.into_reports()
    }

    /// Format the error nicely and add it to the given reporter.
    pub fn add_to_reporter(&self, error: &TcError, reporter: &mut Reporter) {
        let locations = self.stores().location();
        match error {
            TcError::Signal => {}
            TcError::Blocked => {
                let _error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedType)
                    .title("blocked while typechecking".to_string());
            }
            TcError::NeedMoreTypeAnnotationsToInfer { term } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedType)
                    .title("cannot infer the type of this term".to_string());

                if let Some(location) = self.get_location(term) {
                    error
                        .add_span(location)
                        .add_help("consider adding more type annotations to this expression");
                }
            }
            TcError::Compound { errors } => {
                for error in errors {
                    self.add_to_reporter(error, reporter);
                }
            }
            TcError::WrongArgLength { params_id, args_id } => {
                let param_length = params_id.len();
                let arg_length = args_id.len();

                let error =
                    reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                    "mismatch in parameter length: expected {param_length} but got {arg_length}"
                ));

                if let Some(location) = locations.get_overall_location(*params_id) {
                    error
                        .add_span(location)
                        .add_info(format!("expected {param_length} parameters here"));
                }

                if let Some(location) = locations.get_overall_location(*args_id) {
                    error
                        .add_span(location)
                        .add_info(format!("got {arg_length} {} here", args_id.as_str()));
                }
            }
            TcError::WrongDefArgLength { def_params_id: params_id, def_args_id: args_id } => {
                let param_length = params_id.len();
                let arg_length = args_id.len();

                let error = reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                    "mismatch in parameter groups: expected {param_length} groups but got {arg_length}"
                ));

                if let Some(location) = locations.get_overall_location(*params_id) {
                    error
                        .add_span(location)
                        .add_info(format!("expected {param_length} parameter groups here"));
                }

                if let Some(location) = locations.get_overall_location(*args_id) {
                    error
                        .add_span(location)
                        .add_info(format!("got {arg_length} {} groups here", args_id.as_str()));
                }
            }
            TcError::NotAFunction { fn_call, actual_subject_ty } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::InvalidCallSubject)
                    .title("the subject of this function call is not a function");
                if let Some(location) = locations.get_location(fn_call) {
                    error.add_labelled_span(
                        location,
                        format!(
                            "cannot use this as a subject of a function call. It is of type `{}` which is not a function type.",
                            self.env().with(*actual_subject_ty)
                        )
                    );
                }
            }
            TcError::CannotDeref { subject, actual_subject_ty } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::InvalidCallSubject)
                    .title("the subject of this dereference is not a reference");
                if let Some(location) = locations.get_location(subject) {
                    error.add_labelled_span(
                        location,
                        format!(
                            "cannot use this as a subject of a dereference operation. It is of type `{}` which is not a reference type.",
                            self.env().with(*actual_subject_ty)
                        )
                    );
                }
            }
            TcError::MismatchingTypes { expected, actual } => {
                let error = reporter.error().code(HashErrorCode::TypeMismatch).title(format!(
                    "expected type `{}` but got `{}`",
                    self.env().with(*expected),
                    self.env().with(*actual),
                ));
                if let Some(location) = locations.get_location(expected) {
                    error.add_labelled_span(
                        location,
                        format!(
                            "this expects type `{}`", //@@Todo: flag for if inferred or declared
                            self.env().with(*expected)
                        ),
                    );
                }
                if let Some(location) = locations.get_location(actual) {
                    error.add_labelled_span(
                        location,
                        format!("this is of type `{}`", self.env().with(*actual)),
                    );
                }
            }
            TcError::UndecidableEquality { a, b } => {
                let error = reporter.error().code(HashErrorCode::TypeMismatch).title(format!(
                    "cannot determine if expressions `{}` and `{}` are equal",
                    self.env().with(*a),
                    self.env().with(*b),
                ));
                if let Some(location) = locations.get_location(a) {
                    error.add_labelled_span(
                        location,
                        format!(
                            "`{}` from here", //@@Todo: flag for if inferred or declared
                            self.env().with(*a)
                        ),
                    );
                }
                if let Some(location) = locations.get_location(b) {
                    error.add_labelled_span(
                        location,
                        format!("`{}` from here", self.env().with(*b)),
                    );
                }
            }
            TcError::InvalidRangePatternLiteral { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::TypeMismatch)
                    .title("range patterns should contain valid literals");
                if let Some(location) = locations.get_location(location) {
                    error.add_labelled_span(location, "not a valid range literal");
                }
            }
        }
    }
}
