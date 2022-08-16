//! Contains utilities to convert a [super::error::TcError] into a
//! [hash_reporting::report::Report].

use hash_ast::ast::{MatchOrigin, ParamOrigin, RangeEnd};
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_utils::{printing::SequenceDisplay, store::Store};
use itertools::Itertools;

use super::{
    error::TcError,
    params::{ParamListKind, ParamUnificationErrorReason},
};
use crate::{
    fmt::PrepareForFormatting,
    storage::{
        primitives::{AccessOp, Arg, Param, PatArg},
        AccessToStorage, StorageRef,
    },
};

/// A [TcError] with attached typechecker storage.
pub(crate) struct TcErrorWithStorage<'tc> {
    pub error: TcError,
    pub storage: StorageRef<'tc>,
}

impl<'tc> TcErrorWithStorage<'tc> {
    /// Create a new [TcErrorWithStorage]
    pub fn new(error: TcError, storage: StorageRef<'tc>) -> Self {
        Self { error, storage }
    }
}

impl<'tc> AccessToStorage for TcErrorWithStorage<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> From<TcErrorWithStorage<'tc>> for Report {
    fn from(err: TcErrorWithStorage<'tc>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match &err.error {
            TcError::CannotUnify { src, target } => {
                builder.with_error_code(HashErrorCode::TypeMismatch).with_message(format!(
                    "types mismatch, wanted `{}`, but got `{}`",
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
            TcError::CannotUnifyArgs { src_args_id, target_args_id, reason, src, target } => {
                let src_args = err.args_store().get_owned_param_list(*src_args_id);
                let target_args = err.args_store().get_owned_param_list(*target_args_id);

                // It doesn't matter whether we use `src` or `target` since they should be the
                // same
                let origin = err.args_store().get_origin(*src_args_id);

                match &reason {
                    ParamUnificationErrorReason::LengthMismatch => {
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} arguments, however {} arguments were given",
                                origin,
                                target_args.len(),
                                src_args.len()
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(target) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "this {} expects {} arguments...",
                                    origin,
                                    target_args.len(),
                                ),
                            )));
                        }

                        // Provide information about the source of the unification error
                        if let Some(location) = err.location_store().get_location(src) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("...but got {} arguments here", src_args.len()),
                            )));
                        }
                    }
                    ParamUnificationErrorReason::NameMismatch(index) => {
                        // We know that the error occurred at the particular index of both argument
                        // lists.
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!("{} argument names are mis-matching", origin,));

                        let src_arg = &src_args.positional()[*index];
                        let target_arg = &target_args.positional()[*index];

                        // Generate error messages for both the source and target terms, and
                        // optionally a suggestion.
                        let (src_message, target_message, suggestion) =
                            match (src_arg.name, target_arg.name) {
                                (Some(src_name), Some(target_name)) => (
                                    format!("this argument should be named `{}`", target_name),
                                    "argument is specified as being named".to_string(),
                                    format!(
                                        "consider renaming `{}` to `{}`",
                                        src_name, target_name
                                    ),
                                ),
                                (Some(src_name), None) => (
                                    format!("this argument shouldn't be named `{}`", src_name),
                                    "argument is not named".to_string(),
                                    "consider removing the name from the argument".to_string(),
                                ),
                                (None, Some(target_name)) => (
                                    format!("this argument should be named `{}`", target_name),
                                    "argument is specified as being named".to_string(),
                                    format!(
                                        "consider adding `{}` as the name to the argument",
                                        target_name
                                    ),
                                ),
                                _ => unreachable!(),
                            };

                        let src_location =
                            err.location_store().get_location((*src_args_id, *index));
                        let target_location =
                            err.location_store().get_location((*target_args_id, *index));

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
            TcError::CannotUnifyParams { src_params_id, target_params_id, reason, src, target } => {
                let src_params = err.params_store().get_owned_param_list(*src_params_id);
                let target_params = err.params_store().get_owned_param_list(*target_params_id);

                // It doesn't matter whether we use `src` or `target` since they should be the
                // same
                let origin = err.params_store().get_origin(*src_params_id);

                match &reason {
                    ParamUnificationErrorReason::LengthMismatch => {
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} parameters, however {} parameters were given",
                                origin,
                                target_params.len(),
                                src_params.len()
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(*target) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "this {} expects {} parameters...",
                                    origin,
                                    target_params.len(),
                                ),
                            )));
                        }

                        // Provide information about the source of the unification error
                        if let Some(location) = err.location_store().get_location(*src) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("...but got {} parameters here", src_params.len()),
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
            TcError::NotATyFn { term } => {
                builder.with_error_code(HashErrorCode::TyIsNotTyFn).with_message(format!(
                    "type `{}` is not a type function",
                    term.for_formatting(err.global_storage())
                ));

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
            TcError::MismatchingArgParamLength {
                args_kind: args,
                params_id,
                params_location,
                args_location,
            } => {
                let params = err.params_store().get_owned_param_list(*params_id);

                builder.with_error_code(HashErrorCode::ParameterLengthMismatch);

                let params_origin = err.params_store().get_origin(*params_id);

                match params_origin {
                    ParamOrigin::Struct => {
                        // @@ErrorReporting: Get the name of the struct...

                        if params.len() > args.len(err.global_storage()) {
                            let p = ParamListKind::Params(*params_id);
                            let missing_fields =
                                p.compute_missing_fields(args, err.global_storage());

                            builder.with_message(format!(
                                "struct literal is missing the fields {}",
                                SequenceDisplay::all(missing_fields.as_slice())
                            ));

                            // Add note about what fields are missing from the struct
                            if let Some(location) =
                                err.location_store().get_location(*args_location)
                            {
                                builder.add_element(ReportElement::CodeBlock(
                                    ReportCodeBlock::new(
                                        location,
                                        format!(
                                            "missing {}",
                                            SequenceDisplay::all(missing_fields.as_slice())
                                        ),
                                    ),
                                ));
                            }
                        } else {
                            // Compute fields that shouldn't be present here...
                            let p = ParamListKind::Params(*params_id);
                            let extra_fields =
                                args.compute_missing_fields(&p, err.global_storage());

                            builder.with_message(format!(
                                "struct literal does not have the fields {}",
                                SequenceDisplay::all(extra_fields.as_slice())
                            ));

                            // Add note about what fields shouldn't be there
                            // @@Future: It would be nice to highlight the exact fields and just
                            // show them specifically rather than the whole subject expression...
                            if let Some(location) =
                                err.location_store().get_location(*args_location)
                            {
                                builder.add_element(ReportElement::CodeBlock(
                                    ReportCodeBlock::new(
                                        location,
                                        format!(
                                            "fields {} do not exist on this struct",
                                            SequenceDisplay::all(extra_fields.as_slice())
                                        ),
                                    ),
                                ));
                            }
                        }

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(*params_location)
                        {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                "the struct is defined here",
                            )));
                        }
                    }
                    _ => {
                        let arg_length = args.len(err.global_storage());

                        // @@ErrorReporting: get more customised messages for other variant
                        // mismatch...
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} arguments, however {} arguments were given",
                                params_origin,
                                params.len(),
                                arg_length
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(*args_location) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("got {} arguments here...", arg_length),
                            )));
                        }

                        // Provide information about the location of the target type if available
                        if let Some(location) = err.location_store().get_location(*params_location)
                        {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("...but this expects {} arguments.", arg_length),
                            )));
                        }
                    }
                }
            }
            TcError::ParamNotFound { args_kind, params_id, params_subject, name } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedSymbol)
                    .with_message(format!("parameter with name `{}` is not defined", name));

                // find the parameter and report the location
                let id = args_kind.get_name_index(*name, err.global_storage()).unwrap();

                // Provide information about the location of the target type if available
                if let Some(location) = args_kind.field_location(id, err.location_store()) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("{} `{}` not defined", args_kind.as_noun(), name),
                    )));
                }

                // Provide information about the location of the target type if available
                if let Some(location) = err.location_store().get_location(*params_subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "the {} is defined here",
                            err.params_store().get_origin(*params_id)
                        ),
                    )));
                }
            }
            TcError::ParamGivenTwice { param_kind, index } => {
                let origin = param_kind.origin(err.global_storage());

                // we want to get the particular argument at the specified index, get the name
                // and then later use the name to find the original use so that it can be
                // added to the report.
                //
                // Safety: this should be safe to unwrap otherwise we can't detect this issue.
                let (name, first_use) = match param_kind {
                    ParamListKind::Params(id) => {
                        let params = err.params_store().get_owned_param_list(*id);

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
                    ParamListKind::Args(id) => {
                        let args = err.args_store().get_owned_param_list(*id);

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
                    ParamListKind::PatArgs(id) => {
                        let args = err.pat_args_store().get_owned_param_list(*id);

                        // Extract the name from the argument
                        let PatArg { name, .. } = args.positional()[*index];
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

                builder.with_error_code(HashErrorCode::ParameterInUse).with_message(format!(
                    "parameter with name `{}` is already specified within the {}",
                    name, origin
                ));

                // Report where the secondary use occurred, and if possible the first use
                if let Some(location) = param_kind.field_location(*index, err.location_store()) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("parameter `{}` has already been used", name),
                    )));
                }

                if let Some(location) = param_kind.field_location(first_use, err.location_store()) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "initial use occurs here",
                    )));
                }
            }
            // @@ErrorReporting: this could be delegated to semantic-analysis...
            TcError::AmbiguousArgumentOrdering { param_kind, index } => {
                let origin = param_kind.origin(err.global_storage());

                builder
                    .with_error_code(HashErrorCode::AmbiguousFieldOrder)
                    .with_message(format!("ambiguous parameter ordering within a {}", origin));

                // Add the location of the
                if let Some(location) = param_kind.field_location(*index, err.location_store()) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "un-named parameters cannot appear after named parameters",
                    )));
                }
            }
            TcError::UnresolvedNameInValue { name, op, value } => {
                // @@ErrorReporting: Add the span of `name` to show where the access occurs
                let op_member_kind = if *op == AccessOp::Namespace { "member" } else { "field" };

                builder.with_error_code(HashErrorCode::UnresolvedNameInValue).with_message(
                    format!(
                        "the {op_member_kind} `{}` is not present within `{}`",
                        name,
                        value.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` does not contain the {} `{}`",
                            value.for_formatting(err.global_storage()),
                            op,
                            name
                        ),
                    )));
                }
            }
            TcError::UnresolvedVariable { name, value } => {
                builder.with_error_code(HashErrorCode::UnresolvedSymbol).with_message(format!(
                    "variable `{}` is not defined in the current scope",
                    name
                ));

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "variable not defined in the current scope",
                    )));
                }
            }
            TcError::UnsupportedAccess { name, value } => {
                builder
                    .with_error_code(HashErrorCode::UnsupportedAccess)
                    .with_message("unsupported access");

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` cannot be accessed using with the name `{}`",
                            value.for_formatting(err.global_storage()),
                            name
                        ),
                    )));
                }
            }
            TcError::UnsupportedNamespaceAccess { name, value } => {
                builder.with_error_code(HashErrorCode::UnsupportedNamespaceAccess).with_message(
                    format!(
                        "unsupported namespace access, `{}` cannot be namespaced",
                        value.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` cannot be namespaced using with the name `{}`",
                            value.for_formatting(err.global_storage()),
                            name
                        ),
                    )));
                }
            }

            TcError::UnsupportedPropertyAccess { name, value } => {
                builder.with_error_code(HashErrorCode::UnsupportedPropertyAccess).with_message(
                    format!(
                        "unsupported property access for type `{}`",
                        value.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "the property `{}` cannot be accessed from `{}`, it does not support property accessing",
                            name,
                            value.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnApplication { type_fn, cases, unification_errors, .. } => {
                builder.with_error_code(HashErrorCode::TypeMismatch).with_message(format!(
                    "the type function `{}` cannot be applied",
                    type_fn.for_formatting(err.global_storage()),
                ));

                // Now we show where the unification shouldn't occur
                if let Some(location) = err.location_store().get_location(type_fn) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "couldn't apply type function due to a type mismatch".to_string(),
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    ReportNoteKind::Note,
                    format!(
                        "attempted to match {} implementations, they failed due to:",
                        cases.len()
                    ),
                )));

                // Generate the inner `unification_errors` and merge them with the base builder
                // report.
                let _inner_reports: Vec<Report> = unification_errors
                    .iter()
                    .map(|error| TcErrorWithStorage::new(error.clone(), err.storages()).into())
                    .collect();

                // @@Todo(feds01): Now we need to merge the reports:
            }
            TcError::InvalidMergeElement { term } => {
                builder
                    .with_error_code(HashErrorCode::InvalidMergeElement)
                    .with_message("invalid element within a merge declaration");

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within a merge declaration",
                            term.for_formatting(err.global_storage()),
                        ),
                    )));

                    // @@Todo(feds01): add more helpful information about why
                    // this particular type cannot be
                    // used within this position
                }
            }
            TcError::InvalidUnionElement { term } => {
                builder
                    .with_error_code(HashErrorCode::InvalidUnionElement)
                    .with_message("invalid element within a union");

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within a union",
                            term.for_formatting(err.global_storage()),
                        ),
                    )));

                    // @@Todo(feds01): add more helpful information about why
                    // this particular type cannot be used
                    // within this position
                }
            }
            TcError::InvalidTyFnParamTy { param_ty } => {
                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message("invalid function parameter type".to_string());

                if let Some(location) = err.location_store().get_location(param_ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within as the type of a function parameter",
                            param_ty.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnReturnTy { return_ty } => {
                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message("invalid function return type".to_string());

                if let Some(location) = err.location_store().get_location(return_ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` as the return type of a function",
                            return_ty.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnReturnValue { return_value } => {
                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message("invalid type of function return value".to_string());

                if let Some(location) = err.location_store().get_location(return_value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this can't be used as the return of the function",
                    )));

                    // @@Todo(feds01): more information about why this is disallowed
                    builder.add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        format!(
                            "the type of the return value `{}` which is disallowed",
                            return_value.for_formatting(err.global_storage()),
                        ),
                    )));
                }
            }
            TcError::MergeShouldOnlyContainOneNominal {
                merge_term,
                initial_term,
                offending_term,
            } => {
                builder.with_error_code(HashErrorCode::DisallowedType).with_message(
                    "merge declarations should only contain a single nominal term".to_string(),
                );

                if let Some(location) = err.location_store().get_location(initial_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "the merge declaration has an initial nominal term here",
                    )));
                }

                if let Some(location) = err.location_store().get_location(offending_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "...and the second nominal term use occurs here",
                    )));
                }

                // Add the location of the actual merge for annotation
                if let Some(location) = err.location_store().get_location(merge_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "within this merge term",
                    )));
                }
            }

            TcError::MergeShouldBeLevel1 { merge_term, offending_term } => {
                let location = err.location_store().get_location(merge_term).unwrap();

                let offender = err.term_store().get(*offending_term);
                let offender_location = err.location_store().get_location(offending_term).unwrap();

                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message(
                        "this merge declaration should only contain level-1 terms".to_string(),
                    )
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "in this merge declaration",
                    )))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        offender_location,
                        format!(
                            "this term is of {} and not level-1",
                            offender.get_term_level(err.term_store())
                        ),
                    )));
            }
            TcError::MergeShouldBeLevel2 { merge_term, offending_term } => {
                let location = err.location_store().get_location(merge_term).unwrap();

                let offender = err.term_store().get(*offending_term);
                let offender_location = err.location_store().get_location(offending_term).unwrap();

                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message(
                        "this merge declaration should only contain level-2 terms".to_string(),
                    )
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "in this merge declaration",
                    )))
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        offender_location,
                        format!(
                            "this term is of {} and not level-2",
                            offender.get_term_level(err.term_store())
                        ),
                    )));
            }
            TcError::NeedMoreTypeAnnotationsToResolve { term } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedType)
                    .with_message("insufficient information to resolve types".to_string());

                if let Some(location) = err.location_store().get_location(term) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")))
                        .add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Help,
                            "consider adding more type annotations to this expression",
                        )));
                }
            }
            TcError::TermIsNotRuntimeInstantiable { term } => {
                builder.with_error_code(HashErrorCode::NonRuntimeInstantiable).with_message(
                    format!(
                        "the type `{}` is not runtime instantiable",
                        term.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "cannot use this as it isn't runtime instantiable",
                    )));
                }
            }
            TcError::UnsupportedTyFnApplication { subject_id } => {
                builder
                    .with_error_code(HashErrorCode::UnsupportedTyFnApplication)
                    .with_message("unsupported subject in type function application");

                if let Some(location) = err.location_store().get_location(subject_id) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this cannot be used to as the subject to a type function application",
                    )));
                }
            }
            TcError::AmbiguousAccess { access, results } => {
                builder
                    .with_error_code(HashErrorCode::AmbiguousAccess)
                    .with_message(format!("ambiguous access of {} `{}`", access.op, access.name));

                // show the subject if possible
                if let Some(location) = err.location_store().get_location(access.subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "ambiguous access occurs here",
                    )));
                }

                // render the results that the resolver found for additional context
                builder.add_element(ReportElement::Note(ReportNote::new(
                    ReportNoteKind::Note,
                    format!(
                        "the {} access yielded the following results:\n{}",
                        access.op,
                        results
                            .iter()
                            .map(|result| format!(
                                "\t\t{}",
                                result.for_formatting(err.global_storage())
                            ))
                            .collect::<Vec<_>>()
                            .join("\n")
                    ),
                )));
            }
            TcError::InvalidPropertyAccessOfNonMethod { subject, property } => {
                builder
                    .with_error_code(HashErrorCode::InvalidPropertyAccessOfNonMethod)
                    .with_message(format!(
                        "property `{}` access yields non-method result",
                        property
                    ));

                if let Some(location) = err.location_store().get_location(subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this is not a method",
                    )));
                }
            }
            TcError::UninitialisedMemberNotAllowed { member_ty } => {
                builder
                    .with_error_code(HashErrorCode::UninitialisedMember)
                    .with_message("members must be initialised in the current scope");

                if let Some(location) = err.location_store().get_location(member_ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this declaration must be initialised",
                    )));
                }
            }
            TcError::CannotImplementNonTrait { term } => {
                builder.with_error_code(HashErrorCode::TypeIsNotTrait).with_message(format!(
                    "type `{}` is not a trait",
                    term.for_formatting(err.global_storage())
                ));

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this cannot be implemented because it's not a trait",
                    )));
                }
            }
            TcError::TraitImplMissingMember {
                trt_impl_term_id,
                trt_def_term_id,
                trt_def_missing_member_term_id,
            } => {
                builder.with_error_code(HashErrorCode::TraitImplMissingMember).with_message(
                    format!(
                        "trait `{}` is missing the member `{}`",
                        trt_def_term_id.for_formatting(err.global_storage()),
                        trt_def_missing_member_term_id.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(trt_impl_term_id) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "the implementation of trait `{}` is missing the member `{}`",
                            trt_def_term_id.for_formatting(err.global_storage()),
                            trt_def_missing_member_term_id.for_formatting(err.global_storage())
                        ),
                    )));
                }

                // Add the location of the trait definition
                if let Some(location) = err.location_store().get_location(trt_def_term_id) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "trait defined here",
                    )));
                }

                // Add the location of the missing member definition if possible
                if let Some(location) =
                    err.location_store().get_location(trt_def_missing_member_term_id)
                {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "missing member `{}` is defined here",
                            trt_def_missing_member_term_id.for_formatting(err.global_storage())
                        ),
                    )));
                }
            }
            TcError::InvalidCallSubject { term } => {
                // @@Todo: error code
                builder.with_message(format!(
                    "cannot use `{}` as a function call subject",
                    term.for_formatting(err.global_storage())
                ));

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this cannot be called because it's not function-like",
                    )));
                }
            }
            TcError::CannotPatMatchWithoutAssignment { pat } => {
                // @@Todo: error code
                builder.with_message(
                    "declaration left-hand side cannot contain a pattern if no value is provided"
                        .to_string(),
                );

                if let Some(location) = err.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "pattern `{}` is given here on an unset declaration",
                            pat.for_formatting(err.global_storage())
                        ),
                    )));
                }
            }
            TcError::InvalidAssignSubject { location } => {
                builder.with_error_code(HashErrorCode::InvalidAssignSubject).with_message(
                    "assignment left-hand side needs to be a stack variable".to_string(),
                );

                if let Some(location) = err.location_store().get_location(*location) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "non-variable term given in an assignment here",
                    )));
                }
            }
            TcError::NoConstructorOnType { subject } => {
                builder.with_message(format!(
                    "type `{}` has no instantiable constructor",
                    subject.for_formatting(err.global_storage())
                ));

                if let Some(location) = err.location_store().get_location(subject) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::IdentifierBoundMultipleTimes { name, pat } => {
                builder.with_error_code(HashErrorCode::IdentifierBoundMultipleTimes).with_message(
                    format!("identifier `{}` is bound multiple times in the same pattern", name),
                );

                if let Some(location) = err.location_store().get_location(pat) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::MissingPatternBounds { pat, bounds } => {
                builder.with_error_code(HashErrorCode::MissingPatternBounds).with_message(format!(
                    "variables {} are not declared in all patterns",
                    SequenceDisplay::all(bounds.as_slice())
                ));

                if let Some(location) = err.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("pattern doesn't bind {}", SequenceDisplay::all(bounds.as_slice())),
                    )));
                }
            }
            TcError::RefutablePat { pat, origin, uncovered_pats } => {
                let origin = match origin {
                    Some(inner) => match inner {
                        MatchOrigin::Match => "`match`",
                        MatchOrigin::If => "`if`",
                        MatchOrigin::For => "`for-loop`",
                        MatchOrigin::While => "`while` binding",
                    },
                    None => "declaration",
                };

                // Prepare patterns for printing
                let uncovered = uncovered_pats
                    .iter()
                    .map(|id| format!("{}", id.for_formatting(err.global_storage())))
                    .collect_vec();

                let pats = SequenceDisplay::all(&uncovered);

                builder.with_error_code(HashErrorCode::RefutablePat).with_message(format!(
                    "refutable pattern in {origin} binding: {pats} not covered",
                ));

                if let Some(location) = err.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("pattern {pats} not covered"),
                    )));
                }
            }
            TcError::NonExhaustiveMatch { term, uncovered_pats } => {
                let uncovered = uncovered_pats
                    .iter()
                    .map(|id| format!("{}", id.for_formatting(err.global_storage())))
                    .collect_vec();

                let pats = SequenceDisplay::all(&uncovered);

                builder
                    .with_error_code(HashErrorCode::NonExhaustiveMatch)
                    .with_message(format!("non-exhaustive patterns: {} not covered", pats));

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("pattern {} not covered", pats),
                    )));
                }
            }
            TcError::InvalidRangePatBoundaries { end, term } => {
                let message = match end {
                    RangeEnd::Included => {
                        "lower range bound must be less than or equal to upper bound"
                    }
                    RangeEnd::Excluded => "lower range bound must be less than upper bound",
                };

                builder
                    .with_error_code(HashErrorCode::InvalidRangePatBoundaries)
                    .with_message(message);

                if let Some(location) = err.location_store().get_location(term) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::UnsupportedRangePatTy { term } => {
                builder.with_error_code(HashErrorCode::InvalidRangePatBoundaries).with_message(
                    format!(
                        "the type `{}` is not supported in range patterns",
                        term.for_formatting(err.global_storage())
                    ),
                );

                if let Some(location) = err.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        ""
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        "this type is not yet supported because it is an un-sized integer type."
                    )));
                }
            }
        };

        builder.build()
    }
}
