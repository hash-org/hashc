//! Error-related data structures for errors that occur during typechecking.
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    self,
    reporter::{Reporter, Reports},
};
use hash_source::location::SourceLocation;
use hash_types::new::{
    defs::DefParamsId, environment::env::AccessToEnv, params::ParamsId, symbols::Symbol,
    terms::TermId, tys::TyId, utils::common::CommonUtils,
};
use hash_utils::store::SequenceStoreKey;

use super::params::{SomeArgsId, SomeDefArgsId};
use crate::new::{
    environment::tc_env::{AccessToTcEnv, WithTcEnv},
    passes::resolution::scoping::ContextKind,
};

/// An error that occurs during typechecking.
#[derive(Clone, Debug)]
pub enum TcError {
    /// A series of errors.
    Compound { errors: Vec<TcError> },
    /// An error exists, this is just a signal to stop typechecking.
    Signal,
    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },
    /// Traits are not yet supported.
    TraitsNotSupported { trait_location: SourceLocation },
    /// Merge declarations are not yet supported.
    MergeDeclarationsNotSupported { merge_location: SourceLocation },
    /// Some specified symbol was not found.
    SymbolNotFound { symbol: Symbol, location: SourceLocation, looking_in: ContextKind },
    /// Cannot use a module in a value position.
    CannotUseModuleInValuePosition { location: SourceLocation },
    /// Cannot use a module in a type position.
    CannotUseModuleInTypePosition { location: SourceLocation },
    /// Cannot use a module in a pattern position.
    CannotUseModuleInPatternPosition { location: SourceLocation },
    /// Cannot use a data type in a value position.
    CannotUseDataTypeInValuePosition { location: SourceLocation },
    /// Cannot use a data type in a pattern position.
    CannotUseDataTypeInPatternPosition { location: SourceLocation },
    /// Cannot use a constructor in a type position.
    CannotUseConstructorInTypePosition { location: SourceLocation },
    /// Cannot use a function in type position.
    CannotUseFunctionInTypePosition { location: SourceLocation },
    /// Cannot use a function in a pattern position.
    CannotUseFunctionInPatternPosition { location: SourceLocation },
    /// Cannot use the subject as a namespace.
    InvalidNamespaceSubject { location: SourceLocation },
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
}

pub type TcResult<T> = Result<T, TcError>;

impl<'tc> From<WithTcEnv<'tc, &TcError>> for Reports {
    fn from(ctx: WithTcEnv<'tc, &TcError>) -> Self {
        let mut builder = Reporter::new();
        ctx.add_to_reporter(&mut builder);
        builder.into_reports()
    }
}

impl<'tc> WithTcEnv<'tc, &TcError> {
    /// Format the error nicely and add it to the given reporter.
    fn add_to_reporter(&self, reporter: &mut Reporter) {
        let locations = self.tc_env().stores().location();
        match &self.value {
            TcError::Signal => {}
            TcError::NeedMoreTypeAnnotationsToInfer { term } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedType)
                    .title("cannot infer the type of this term".to_string());

                if let Some(location) = self.tc_env().get_location(term) {
                    error
                        .add_span(location)
                        .add_help("consider adding more type annotations to this expression");
                }
            }
            TcError::Compound { errors } => {
                for error in errors {
                    self.tc_env().with(error).add_to_reporter(reporter);
                }
            }
            TcError::TraitsNotSupported { trait_location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnsupportedTraits)
                    .title("traits are work-in-progress and currently not supported".to_string());

                error.add_span(*trait_location).add_help("cannot use traits yet");
            }
            TcError::MergeDeclarationsNotSupported { merge_location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnsupportedTraits)
                    .title("merge declarations are currently not supported".to_string());

                error.add_span(*merge_location).add_help("cannot use merge declarations yet");
            }
            TcError::SymbolNotFound { symbol, location, looking_in } => {
                let def_name = format!("{}", self.tc_env().with(looking_in));
                let search_name = self.tc_env().env().with(*symbol);
                let noun = match looking_in {
                    ContextKind::Access(_, _) => "member",
                    ContextKind::Environment => "name",
                };
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedSymbol)
                    .title(format!("cannot find {noun} `{search_name}` in {def_name}"));
                error.add_labelled_span(
                    *location,
                    format!("tried to look for {noun} `{search_name}` in {def_name}",),
                );

                if let ContextKind::Access(_, def) = looking_in {
                    if let Some(location) = locations.get_location(def) {
                        error.add_span(location).add_info(format!(
                            "{def_name} is defined here, and has no member `{search_name}`",
                        ));
                    }
                }
            }
            TcError::CannotUseModuleInValuePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a module in expression position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a module");
            }
            TcError::CannotUseModuleInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a module in type position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in type position as it is a module");
            }
            TcError::CannotUseModuleInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a module in pattern position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in pattern position as it is a module");
            }
            TcError::CannotUseDataTypeInValuePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a data type in expression position")
                    .add_help("consider using a constructor call instead");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a data type");
            }
            TcError::CannotUseDataTypeInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a data type in pattern position")
                    .add_help("consider using a constructor pattern instead");

                error
                    .add_span(*location)
                    .add_info("cannot use this in pattern position as it is a data type");
            }
            TcError::CannotUseConstructorInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a constructor in type position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in type position as it is a constructor");
            }
            TcError::CannotUseFunctionInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a function in type position");

                error.add_span(*location).add_info(
                    "cannot use this in type position as it refers to a function definition",
                );
            }
            TcError::CannotUseFunctionInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a function in pattern position");

                error.add_span(*location).add_info(
                    "cannot use this in pattern position as it refers to a function definition",
                );
            }
            TcError::InvalidNamespaceSubject { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnsupportedAccess)
                    .title("only data types and modules can be used as namespacing subjects");

                error
                    .add_span(*location)
                    .add_info("cannot use this as a subject of a namespace access");
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
        }
    }
}
