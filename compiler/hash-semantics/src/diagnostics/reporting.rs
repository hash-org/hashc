use hash_reporting::{
    hash_error_codes::error_codes::HashErrorCode,
    reporter::{Reporter, Reports},
};
use hash_tir::tir::HasAstNodeId;
use hash_typecheck::errors::TcErrorReporter;

use super::definitions::{SemanticError, SemanticWarning};
use crate::{env::SemanticEnv, passes::resolution::scoping::ContextKind};

/// Builds [`Reports`] from semantic errors and warnings.
pub struct SemanticReporter;
impl SemanticReporter {
    pub fn make_reports_from_error<E: SemanticEnv>(env: &E, error: SemanticError) -> Reports {
        let mut reporter = Reporter::new();
        Self::add_error_to_reporter(env, &error, &mut reporter);
        reporter.into_reports()
    }

    pub fn make_reports_from_warning(warning: SemanticWarning) -> Reports {
        let mut reporter = Reporter::new();
        Self::add_warning_to_reporter(&warning, &mut reporter);
        reporter.into_reports()
    }

    fn add_warning_to_reporter(warning: &SemanticWarning, reporter: &mut Reporter) {
        match warning {
            SemanticWarning::ExhaustivenessWarning { warning } => {
                warning.add_to_reports(reporter);
            }
            SemanticWarning::Compound { warnings } => {
                for warning in warnings {
                    Self::add_warning_to_reporter(warning, reporter);
                }
            }
        }
    }

    fn add_error_to_reporter<E: SemanticEnv>(
        env: &E,
        error: &SemanticError,
        reporter: &mut Reporter,
    ) {
        // @@ErrorReporting: improve error messages and locations
        match error {
            SemanticError::Signal => {}
            SemanticError::NeedMoreTypeAnnotationsToInfer { term } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedType)
                    .title("cannot infer the type of this term".to_string());

                if let Some(location) = term.span() {
                    error
                        .add_span(location)
                        .add_help("consider adding more type annotations to this expression");
                }
            }
            SemanticError::Compound { errors } => {
                for error in errors {
                    Self::add_error_to_reporter(env, error, reporter);
                }
            }
            SemanticError::SymbolNotFound { symbol, location, looking_in } => {
                let def_name = format!("{}", looking_in);
                let search_name = *symbol;
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
                    if let Some(location) = def.span() {
                        error.add_span(location).add_info(format!(
                            "{def_name} is defined here, and has no member `{search_name}`",
                        ));
                    }
                }
            }
            SemanticError::CannotUseModuleInValuePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a module in expression position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a module");
            }
            SemanticError::CannotUseModuleInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a module in type position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in type position as it is a module");
            }
            SemanticError::CannotUseModuleInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a module in pattern position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in pattern position as it is a module");
            }
            SemanticError::CannotUseDataTypeInValuePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a data type in expression position")
                    .add_help("consider using a constructor call instead");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a data type");
            }
            SemanticError::CannotUseDataTypeInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::NonRuntimeInstantiable)
                    .title("cannot use a data type in pattern position")
                    .add_help("consider using a constructor pattern instead");

                error
                    .add_span(*location)
                    .add_info("cannot use this in pattern position as it is a data type");
            }
            SemanticError::CannotUseConstructorInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a constructor in type position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in type position as it is a constructor");
            }
            SemanticError::CannotUseFunctionInTypePosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a function in type position");

                error.add_span(*location).add_info(
                    "cannot use this in type position as it refers to a function definition",
                );
            }
            SemanticError::CannotUseFunctionInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a function in pattern position");

                error.add_span(*location).add_info(
                    "cannot use this in pattern position as it refers to a function definition",
                );
            }
            SemanticError::CannotUseIntrinsicInPatternPosition { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use an intrinsic in pattern position");

                error.add_span(*location).add_info(
                    "cannot use this in pattern position as it refers to a compiler intrinsic",
                );
            }
            SemanticError::CannotUseNonConstantItem { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot use a non-constant value in constant position");

                error.add_span(*location).add_info(
                    "cannot use this in constant position as it refers to a runtime value",
                );
            }
            SemanticError::InvalidNamespaceSubject { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnsupportedAccess)
                    .title("only data types and modules can be used as namespacing subjects");

                error
                    .add_span(*location)
                    .add_info("cannot use this as a subject of a namespace access");
            }
            SemanticError::TypeError { error } => TcErrorReporter::add_to_reporter(error, reporter),
            SemanticError::UnexpectedArguments { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("unexpected arguments given to subject");

                error
                    .add_span(*location)
                    .add_info("cannot use these arguments as the subject does not expect them");
            }
            SemanticError::DataDefIsNotSingleton { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("cannot construct this data type directly because it is an enum");

                error
                    .add_span(*location)
                    .add_info("you need to specify which variant of this data type you want");
            }
            SemanticError::EntryPointNotFound => {
                let error = reporter.error().title("no entry point specified");
                error.add_note(
                    "when building an executable, an entry point must be specified in the source.\nThis can be done by using the `main` keyword, or by using the `#entry_point` directive."
                );
            }
            SemanticError::ModulePatternsNotSupported { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::MissingPatBind)
                    .title("module patterns are not supported yet");

                error
                    .add_span(*location)
                    .add_info("cannot use a module pattern yet. Instead, bind to a name and access members through `::`");
            }
            SemanticError::EnumTypeAnnotationMustBeOfDefiningType { location } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ValueCannotBeUsedAsType)
                    .title("enum type annotation must be of the defining type");

                error.add_span(*location).add_info(
                    "cannot use this type annotation as it is not the defining type of the enum",
                );
            }
            SemanticError::EnumDiscriminantOverflow {
                location,
                discriminant,
                annotation_origin,
            } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::EnumDiscriminantOverflowed)
                    .title("enum discriminant overflowed")
                    .add_span(*location)
                    .add_note(format!("the type of the discriminant is {}", discriminant.ty));

                if let Some(annotation_origin) = annotation_origin {
                    error.add_labelled_span(
                        *annotation_origin,
                        "discriminant type was specified here",
                    );
                }
            }
            SemanticError::DuplicateEnumDiscriminant { original, offending, value } => {
                let value_fmt = value.to_string(env);

                reporter
                    .error()
                    .code(HashErrorCode::DuplicateEnumDiscriminant)
                    .title(format!("discriminant value `{value_fmt}` assigned more than once"))
                    .add_labelled_span(*original, format!("`{value_fmt}` originally assigned here"))
                    .add_labelled_span(*offending, format!("`{value_fmt}` assigned here"));
            }
            SemanticError::ExhaustivenessError { error } => error.add_to_reports(reporter),
            SemanticError::DuplicateBindInPat { offending, original } => {
                reporter
                    .error()
                    .code(HashErrorCode::DuplicateBindInPat)
                    .title(format!(
                        "variable `{}` is bound more than once in the same pattern",
                        original.name()
                    ))
                    .add_labelled_span(offending.span(), "used in a pattern more than once")
                    .add_labelled_span(original.span(), "first binding of variable");
            }
            SemanticError::MissingPatBind { offending, missing } => {
                reporter
                    .error()
                    .code(HashErrorCode::MissingPatBind)
                    .title(format!("variable `{}` is not bound in all patterns", missing.name()))
                    .add_labelled_span(
                        *offending,
                        format!("pattern doesn't bind `{}`", missing.name()),
                    )
                    .add_labelled_span(missing.span(), "variable not in all patterns");
            }
            SemanticError::MismatchingPatBind { original, offending } => {
                reporter
                    .error()
                    .code(HashErrorCode::MismatchingPatBind)
                    .title(format!(
                        "variable `{}` is bound inconsistently across or-patterns",
                        original.name()
                    ))
                    .add_labelled_span(original.span(), "first binding of variable")
                    .add_labelled_span(offending.span(), "bound differently");
            }
        }
    }
}
