//! Contains utilities to convert a [crate::error::TcError] into a
//! [hash_reporting::report::Report].
use crate::{
    error::{ParamUnificationErrorReason, ParameterListOrigin, TcError},
    fmt::PrepareForFormatting,
    storage::{
        primitives::{Arg, Param},
        AccessToStorage, StorageRef,
    },
};
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};

/// A [TcError] with attached typechecker storage.
pub(crate) struct TcErrorWithStorage<'gs, 'ls, 'cd> {
    pub error: TcError,
    pub storage: StorageRef<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for TcErrorWithStorage<'gs, 'ls, 'cd> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> From<TcErrorWithStorage<'gs, 'ls, 'cd>> for Vec<Report> {
    fn from(err: TcErrorWithStorage<'gs, 'ls, 'cd>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match &err.error {
            TcError::CannotUnify { src, target } => {
                builder.with_error_code(HashErrorCode::TypeMismatch).with_message(format!(
                    "types mismatch wanted `{}`, but got `{}`",
                    target.for_formatting(err.global_storage()),
                    src.for_formatting(err.global_storage())
                ));

                // Now get the spans for the two terms and add them to the
                // report
                if let Some(location) = err.location_store().get_location(target) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "this expects the type `{}`",
                            target.for_formatting(err.global_storage()),
                        ),
                    )));
                }

                if let Some(location) = err.location_store().get_location(src) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "...but this is of type `{}`",
                            src.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::CannotUnifyParams {
                src_params_id,
                target_params_id,
                origin,
                reason,
                src,
                target,
            } => {
                let src_params = err.params_store().get(*src_params_id);
                let target_params = err.params_store().get(*target_params_id);

                match &reason {
                    ParamUnificationErrorReason::LengthMismatch => {
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects `{}` arguments, however `{}` arguments were given",
                                origin,
                                target_params.len(),
                                src_params.len()
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(target) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "this {} expects `{}` arguments.",
                                    origin,
                                    target.for_formatting(err.global_storage()),
                                ),
                            )));
                        }

                        // Provide information about the source of the unification error
                        if let Some(location) = err.location_store().get_location(src) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                "incorrect number of arguments here",
                            )));
                        }
                    }
                    ParamUnificationErrorReason::NameMismatch(index) => {
                        // We know that the error occurred at the particular index of both parameter
                        // lists.
                        builder
                            .with_error_code(HashErrorCode::ParameterNameMismatch)
                            .with_message(format!("{} parameter names are mis-matching", origin,));

                        let src_param = &src_params.positional()[*index];
                        let target_param = &target_params.positional()[*index];

                        // Generate error messages for both the source and target terms, and
                        // optionally a suggestion.
                        let (src_message, target_message, suggestion) =
                            match (src_param.name, target_param.name) {
                                (Some(src_name), Some(target_name)) => (
                                    format!("this parameter should be named `{}`", target_name),
                                    "parameter is specified as being named".to_string(),
                                    format!(
                                        "consider renaming `{}` to `{}`",
                                        src_name, target_name
                                    ),
                                ),
                                (Some(src_name), None) => (
                                    format!("this parameter shouldn't be named `{}`", src_name),
                                    "parameter is not named".to_string(),
                                    "consider removing the name from the parameter".to_string(),
                                ),
                                (None, Some(target_name)) => (
                                    format!("this parameter should be named `{}`", target_name),
                                    "parameter is specified as being named".to_string(),
                                    format!(
                                        "consider adding `{}` as the name to the parameter",
                                        target_name
                                    ),
                                ),
                                _ => unreachable!(),
                            };

                        let src_location =
                            err.location_store().get_location((*src_params_id, *index));
                        let target_location =
                            err.location_store().get_location((*target_params_id, *index));

                        // Provide information about the location of the target type if available.
                        // If the location is not available, we just attach
                        // it to as a note.
                        if let Some(location) = target_location {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                target_message,
                            )));
                        } else {
                            builder.add_element(ReportElement::Note(ReportNote::new(
                                ReportNoteKind::Note,
                                target_message,
                            )));
                        }

                        // Provide information about the source of the unification error. If the
                        // source is not available (which is unlikely and
                        // possibly an invariant?), then add it as a note to
                        // the report.
                        if let Some(location) = src_location {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                src_message,
                            )));
                        } else {
                            builder.add_element(ReportElement::Note(ReportNote::new(
                                ReportNoteKind::Note,
                                src_message,
                            )));
                        }

                        // Append the suggestion
                        builder.add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Help,
                            suggestion,
                        )));
                    }
                }
            }
            TcError::NotATypeFunction { term } => {
                builder.with_error_code(HashErrorCode::TypeIsNotTypeFunction).with_message(
                    format!(
                        "type `{}` is not a type function",
                        term.for_formatting(err.global_storage())
                    ),
                );

                // Get the location of the term
                // @@Future: is it useful to also print the location of what was expecting
                // something to be a type function.
                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this type is not a type function",
                    )));
                }
            }
            TcError::CannotUseValueAsTy { value } => {
                builder.with_error_code(HashErrorCode::ValueCannotBeUsedAsType).with_message(
                    format!(
                        "type `{}` is not a type function",
                        value.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this cannot be used a type",
                    )));
                }
            }
            TcError::MismatchingArgParamLength { args, params, target } => {
                let params = err.params_store().get(*params);
                let args = err.args_store().get(*args);

                builder.with_error_code(HashErrorCode::ParameterLengthMismatch).with_message(
                    format!(
                        "type function application expects `{}` arguments, however `{}` arguments were given",
                        params.len(),
                        args.len()
                    ),
                );

                // Provide information about the location of the target type if available
                if let Some(location) = err.location_store().get_location(target) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "this expects `{}` arguments.",
                            target.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::ParamNotFound { params, name } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedSymbol)
                    .with_message(format!("parameter with name `{}` is not defined", name,));

                // find the parameter and report the location
                let params = err.params_store().get(*params);
                let (_, param) = params.get_by_name(*name).unwrap();

                // Provide information about the location of the target type if available
                if let Some(location) = err.location_store().get_location(param.ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("parameter `{}` not defined", name,),
                    )));
                }
            }
            TcError::ParamGivenTwice { origin, index, .. } => {
                // we want to get the particular argument at the specified index, get the name
                // and then later use the name to find the original use so that it can be
                // added to the report.
                //
                // Safety: this should be safe to unwrap otherwise we can't detect this issue.
                let (name, first_use) = match origin {
                    ParameterListOrigin::Params(id) => {
                        let params = err.params_store().get(*id);

                        // Extract the name from the parameter
                        let Param { name, .. } = params.positional()[*index];
                        let name = name.unwrap();

                        // find the ise of the first name
                        let first_use = params
                            .positional()
                            .iter()
                            .position(|param| param.name == Some(name))
                            .unwrap();

                        (name, first_use)
                    }
                    ParameterListOrigin::Args(id) => {
                        let args = err.args_store().get(*id);

                        // Extract the name from the argument
                        let Arg { name, .. } = args.positional()[*index];
                        let name = name.unwrap();

                        // find the ise of the first name
                        let first_use = args
                            .positional()
                            .iter()
                            .position(|param| param.name == Some(name))
                            .unwrap();

                        (name, first_use)
                    }
                };

                let location_from_origin = |index: usize| match origin {
                    ParameterListOrigin::Params(id) => {
                        err.location_store().get_location((*id, index))
                    }
                    ParameterListOrigin::Args(id) => {
                        err.location_store().get_location((*id, index))
                    }
                };

                builder
                    .with_error_code(HashErrorCode::ParameterInUse)
                    .with_message(format!("parameter with name `{}` is already specified", name,));

                // Report where the secondary use occurred, and if possible the first use
                if let Some(location) = location_from_origin(*index) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("parameter `{}` has already been used", name),
                    )));
                }

                if let Some(location) = location_from_origin(first_use) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "initial use occurs here",
                    )));
                }
            }
            _ => {
                // @@Temporary
                builder.with_message(format!("not yet pretty error: {:#?}", err.error));
            }
        };

        vec![builder.build()]
    }
}
