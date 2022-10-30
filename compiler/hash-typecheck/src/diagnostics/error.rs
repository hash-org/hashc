//! Error-related data structures for errors that occur during typechecking.

use hash_ast::ast::{MatchOrigin, ParamOrigin, RangeEnd};
use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::identifier::Identifier;
use hash_types::{
    arguments::{ArgOld, ArgsIdOld},
    fmt::{PrepareForFormatting, TcFormatOpts},
    location::LocationTarget,
    params::{AccessOp, Field, Param, ParamsId},
    pats::{PatArg, PatId},
    scope::ScopeId,
    terms::{AccessTermOld, TermId, TyFnCase},
    trts::TrtDefOld,
};
use hash_utils::{
    pluralise,
    printing::{SequenceDisplay, SequenceDisplayOptions, SequenceJoinMode},
    store::CloneStore,
};
use itertools::Itertools;

use super::params::{ParamListKind, ParamUnificationErrorReason};
use crate::{
    ops::AccessToOps,
    storage::{AccessToStorage, StorageRef},
};

/// Convenient type alias for a result with a [TcError] as the error type.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
#[derive(Debug, Clone)]
pub enum TcError {
    /// Cannot unify the two terms.
    CannotUnify { src: TermId, target: TermId },
    // @@Refactor: It would be nice to not have separate variants for `CannotUnifyArgs` and
    // `CannotUnifyParams`.
    /// Cannot unify the two argument lists. This can occur if the names
    /// don't match of the arguments or if the number of arguments isn't the
    /// same.
    CannotUnifyArgs {
        src_args_id: ArgsIdOld,
        target_args_id: ArgsIdOld,
        src: TermId,
        target: TermId,
        reason: ParamUnificationErrorReason,
    },
    /// Cannot unify the two parameter lists. This can occur if the names
    /// don't match of the parameters or if the number of parameters isn't the
    /// same, or the types mismatch.
    CannotUnifyParams {
        src_params_id: ParamsId,
        target_params_id: ParamsId,
        src: LocationTarget,
        target: LocationTarget,
        reason: ParamUnificationErrorReason,
    },
    /// The given term should be a type function but it isn't.
    NotATyFn { term: TermId },
    /// The given value cannot be used as a type.
    CannotUseValueAsTy { value: TermId },
    /// The given arguments do not match the length of the target parameters.
    MismatchingArgParamLength {
        args_kind: ParamListKind,
        params_id: ParamsId,
        params_location: LocationTarget,
        args_location: LocationTarget,
    },
    /// The parameter with the given name is not found in the given parameter
    /// list.
    ParamNotFound { args_kind: ParamListKind, params_subject: LocationTarget, name: Identifier },
    /// There is a argument or parameter (at the index) which is
    /// specified twice in the given argument list.
    ParamGivenTwice { param_kind: ParamListKind, index: usize },
    /// It is invalid to use a positional argument after a named argument.
    AmbiguousArgumentOrdering { param_kind: ParamListKind, index: usize },
    /// The given name cannot be resolved in the given value.
    UnresolvedNameInValue {
        // @@ErrorReporting: add more info about the term. Maybe we need a general way of
        // characterising terms as a string (i.e. "struct", "enum", "module", etc).
        name: Field,
        op: AccessOp,
        value: TermId,
    },
    /// The given variable cannot be resolved in the current context.
    UnresolvedVariable { name: Identifier, value: TermId },
    /// The given value does not support accessing (of the given name).
    UnsupportedAccess { name: Identifier, value: TermId },
    /// The given value does not support namespace accessing (of the given
    /// name).
    UnsupportedNamespaceAccess { name: Field, value: TermId },
    /// The given value does not support property accessing (of the given name).
    UnsupportedPropertyAccess { name: Field, value: TermId },
    /// The given type function cannot be applied to the given arguments, due to
    /// the given errors.
    InvalidTyFnApplication {
        type_fn: TermId,
        cases: Vec<TyFnCase>,
        args: ArgsIdOld,
        unification_errors: Vec<TcError>,
    },
    /// The given term cannot be used in a merge operation.
    InvalidMergeElement { term: TermId },
    /// The given term cannot be used in a union operation.
    InvalidUnionElement { term: TermId },
    /// The given term cannot be used as a type function parameter type.
    InvalidTyFnParamTy { param_ty: TermId },
    /// The given term cannot be used as a type function return type.
    InvalidTyFnReturnTy { return_ty: TermId },
    /// The given term cannot be used as a type function return value.
    InvalidTyFnReturnValue { return_value: TermId },
    /// The given merge term should only contain zero or one nominal elements,
    /// but it contains more.
    MergeShouldOnlyContainOneNominal {
        merge_term: TermId,
        /// The first term
        initial_term: TermId,
        /// Secondary nominal term
        offending_term: TermId,
    },
    /// The given merge term should contain only level 1 terms.
    MergeShouldBeLevel1 { merge_term: TermId, offending_term: TermId },
    /// The given merge term should contain only level 2 terms.
    MergeShouldBeLevel2 { merge_term: TermId, offending_term: TermId },
    /// More type annotations are needed to resolve the given term.
    NeedMoreTypeAnnotationsToResolve { term: TermId },
    /// The given term cannot be instantiated at runtime.
    TermIsNotRuntimeInstantiable { term: TermId },
    /// The given term cannot be used as the subject of a type function
    /// application.
    UnsupportedTyFnApplication { subject_id: TermId },
    /// The given access operation results in more than one result.
    AmbiguousAccess { access: AccessTermOld, results: Vec<TermId> },
    /// Cannot use this as a function call or struct subject.
    InvalidCallSubject { term: TermId },
    /// The given access operation does not resolve to a method.
    InvalidPropertyAccessOfNonMethod { subject: TermId, property: Field },
    /// The given member requires an initialisation in the current scope.
    /// @@ErrorReporting: add span of member.
    UninitialisedMemberNotAllowed { member: LocationTarget },
    /// Cannot implement something that isn't a trait.
    CannotImplementNonTrait { term: TermId },
    /// The trait implementation `trt_impl_term_id` is missing the member
    /// `trt_def_missing_member_id` from the trait `trt_def_term_id`.
    TraitImplMissingMember {
        /// The trait implementation block term.
        trt_impl_term_id: TermId,
        /// The trait definition term.
        trt_def_term_id: TermId,
        /// A list of trait items that were identified as missing from the trait
        /// impl
        missing_trt_members: Vec<usize>,
    },
    /// When a member of an `impl` block that implements a trait is not present
    /// within the trait definition, in other words a non-member.
    MethodNotAMemberOfTrait { trt_def_term_id: TermId, member: LocationTarget, name: Identifier },
    /// Cannot use pattern matching in a declaration without an assignment
    CannotPatMatchWithoutAssignment { pat: PatId },
    /// Cannot use a non-name as an assign subject.
    InvalidAssignSubject { location: LocationTarget },

    /// Cannot find a constructor for the given type
    NoConstructorOnType { subject: TermId },

    /// The subject does not have a callable constructor (i.e. it is constant).
    NoCallableConstructorOnType { subject: TermId },

    /// When a bind within a pattern is declared more than one
    IdentifierBoundMultipleTimes { name: Identifier, pat: PatId },

    /// Within an `or` pattern, where there is a discrepancy between the
    /// declared bounds within two patterns. For example, if one pattern
    /// binds `k`, but the other doesn't.
    MissingPatternBounds { pat: PatId, bounds: Vec<Identifier> },

    /// When a pattern is expected to be irrefutable but was found to be
    /// refutable with provided `witnesses` or possible patterns that are
    /// not covered by the pattern.
    RefutablePat {
        /// The pattern that is refutable
        pat: PatId,
        /// Where the refutability check came from, `for`, `while`, `match`...
        ///
        /// Although we should only really ever get `for` or `None` which means
        /// it's either in a for-loop or a declaration.
        origin: Option<MatchOrigin>,
        /// Generated patterns that are not covered by `pat`
        uncovered_pats: Vec<PatId>,
    },
    /// When a match block is non-exhaustive
    NonExhaustiveMatch {
        /// The term of the subject expression
        term: TermId,
        /// Generated patterns that are not covered by match arms
        uncovered_pats: Vec<PatId>,
    },
    /// When an inclusive range pattern boundaries are invalid
    InvalidRangePatBoundaries {
        /// The kind of range end this pattern has,
        end: RangeEnd,
        /// Term of the range pattern lower bound
        term: TermId,
    },
    /// When an unsized integer literal is specified in the range. This
    /// is currently not supported because the exhaustiveness checking
    /// cannot currently deal with this kind of range.
    UnsupportedRangePatTy { term: TermId },

    /// When a particular scope member is declared as `immutable` but an
    /// attempt was made to perform a mutable operation on this item.
    MemberIsImmutable {
        /// The name of the member
        name: Identifier,
        /// The location of where the modification was being made.
        site: LocationTarget,
        /// The location of the declaration.
        decl: (ScopeId, usize),
    },
    MemberMustBeImmutable {
        /// The name of the member
        name: Identifier,
        /// The location of where the modification was being made.
        site: LocationTarget,
    },
}

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
    fn from(ctx: TcErrorWithStorage<'tc>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match &ctx.error {
            TcError::CannotUnify { src, target } => {
                builder.with_error_code(HashErrorCode::TypeMismatch).with_message(format!(
                    "types mismatch, wanted `{}`, but got `{}`",
                    target.for_formatting(ctx.global_storage()),
                    src.for_formatting(ctx.global_storage())
                ));

                // Now get the spans for the two terms and add them to the
                // report
                if let Some(location) = ctx.location_store().get_location(target) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "this expects the type `{}`",
                            target.for_formatting(ctx.global_storage()),
                        ),
                    )));
                }

                if let Some(location) = ctx.location_store().get_location(src) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "...but this is of type `{}`",
                            src.for_formatting(ctx.global_storage()),
                        ),
                    )));
                }
            }
            TcError::CannotUnifyArgs { src_args_id, target_args_id, reason, src, target } => {
                let src_args = ctx.args_store().get_owned_param_list(*src_args_id);
                let target_args = ctx.args_store().get_owned_param_list(*target_args_id);

                // It doesn't matter whether we use `src` or `target` since they should be the
                // same
                let origin = ctx.args_store().get_origin(*src_args_id);

                match &reason {
                    ParamUnificationErrorReason::LengthMismatch => {
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} argument{}, however {} argument{} were given",
                                origin,
                                target_args.len(),
                                pluralise!(target_args.len()),
                                src_args.len(),
                                pluralise!(src_args.len())
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = ctx.location_store().get_location(target) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "this {} expects {} argument{}...",
                                    origin,
                                    target_args.len(),
                                    pluralise!(target_args.len()),
                                ),
                            )));
                        }

                        // Provide information about the source of the unification error
                        if let Some(location) = ctx.location_store().get_location(src) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "...but got {} argument{} here",
                                    src_args.len(),
                                    pluralise!(src_args.len())
                                ),
                            )));
                        }
                    }
                    ParamUnificationErrorReason::NameMismatch(index) => {
                        // We know that the error occurred at the particular index of both argument
                        // lists.
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!("{origin} argument names are mis-matching",));

                        let src_arg = &src_args.positional()[*index];
                        let target_arg = &target_args.positional()[*index];

                        // Generate error messages for both the source and target terms, and
                        // optionally a suggestion.
                        let (src_message, target_message, suggestion) =
                            match (src_arg.name, target_arg.name) {
                                (Some(src_name), Some(target_name)) => (
                                    format!("this argument should be named `{target_name}`"),
                                    "argument is specified as being named".to_string(),
                                    format!(
                                        "consider renaming `{}` to `{}`",
                                        src_name, target_name
                                    ),
                                ),
                                (Some(src_name), None) => (
                                    format!("this argument shouldn't be named `{src_name}`"),
                                    "argument is not named".to_string(),
                                    "consider removing the name from the argument".to_string(),
                                ),
                                (None, Some(target_name)) => (
                                    format!("this argument should be named `{target_name}`"),
                                    "argument is specified as being named".to_string(),
                                    format!(
                                        "consider adding `{}` as the name to the argument",
                                        target_name
                                    ),
                                ),
                                _ => unreachable!(),
                            };

                        let src_location =
                            ctx.location_store().get_location((*src_args_id, *index));
                        let target_location =
                            ctx.location_store().get_location((*target_args_id, *index));

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
                let src_params = ctx.params_store().get_owned_param_list(*src_params_id);
                let target_params = ctx.params_store().get_owned_param_list(*target_params_id);

                // It doesn't matter whether we use `src` or `target` since they should be the
                // same
                let origin = ctx.params_store().get_origin(*src_params_id);

                match &reason {
                    ParamUnificationErrorReason::LengthMismatch => {
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} parameter{}, however {} parameter{} were given",
                                origin,
                                target_params.len(),
                                pluralise!(target_params.len()),
                                src_params.len(),
                                pluralise!(src_params.len())
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = ctx.location_store().get_location(*target) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!(
                                    "this {} expects {} parameter{}...",
                                    origin,
                                    target_params.len(),
                                    pluralise!(target_params.len())
                                ),
                            )));
                        }

                        // Provide information about the source of the unification error
                        if let Some(location) = ctx.location_store().get_location(*src) {
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
                            .with_message(format!("{origin} parameter names are mis-matching",));

                        let src_param = &src_params.positional()[*index];
                        let target_param = &target_params.positional()[*index];

                        // Generate error messages for both the source and target terms, and
                        // optionally a suggestion.
                        let (src_message, target_message, suggestion) =
                            match (src_param.name, target_param.name) {
                                (Some(src_name), Some(target_name)) => (
                                    format!("this parameter should be named `{target_name}`"),
                                    "parameter is specified as being named".to_string(),
                                    format!(
                                        "consider renaming `{}` to `{}`",
                                        src_name, target_name
                                    ),
                                ),
                                (Some(src_name), None) => (
                                    format!("this parameter shouldn't be named `{src_name}`"),
                                    "parameter is not named".to_string(),
                                    "consider removing the name from the parameter".to_string(),
                                ),
                                (None, Some(target_name)) => (
                                    format!("this parameter should be named `{target_name}`"),
                                    "parameter is specified as being named".to_string(),
                                    format!(
                                        "consider adding `{}` as the name to the parameter",
                                        target_name
                                    ),
                                ),
                                _ => unreachable!(),
                            };

                        let src_location =
                            ctx.location_store().get_location((*src_params_id, *index));
                        let target_location =
                            ctx.location_store().get_location((*target_params_id, *index));

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
                    term.for_formatting(ctx.global_storage())
                ));

                // Get the location of the term
                // @@Future: is it useful to also print the location of what was expecting
                // something to be a type function.
                if let Some(location) = ctx.location_store().get_location(term) {
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
                        value.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(value) {
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
                let params = ctx.params_store().get_owned_param_list(*params_id);

                builder.with_error_code(HashErrorCode::ParameterLengthMismatch);

                let params_origin = ctx.params_store().get_origin(*params_id);

                match params_origin {
                    ParamOrigin::Struct => {
                        builder.with_error_code(HashErrorCode::MissingStructField);
                        // @@ErrorReporting: Get the name of the struct...

                        if params.len() > args.len() {
                            let missing_fields = ctx
                                .param_ops()
                                .compute_missing_fields(&ParamListKind::Params(*params_id), args);

                            // Format the missing fields, limit to printing only `5` verbosely
                            let formatted_missing_fields = SequenceDisplay::new(
                                missing_fields.as_slice(),
                                SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 5),
                            );

                            builder.with_message(format!(
                                "struct literal is missing the field{} {formatted_missing_fields}",
                                pluralise!(missing_fields.len()),
                            ));

                            // Add note about what fields are missing from the struct
                            if let Some(location) =
                                ctx.location_store().get_location(*args_location)
                            {
                                builder.add_element(ReportElement::CodeBlock(
                                    ReportCodeBlock::new(
                                        location,
                                        format!("missing {formatted_missing_fields}",),
                                    ),
                                ));
                            }
                        } else {
                            // Compute fields that shouldn't be present here...
                            let extra_fields = ctx
                                .param_ops()
                                .compute_missing_fields(args, &ParamListKind::Params(*params_id));

                            // Format the missing fields, limit to printing only `5` verbosely
                            let formatted_extra_fields = SequenceDisplay::new(
                                extra_fields.as_slice(),
                                SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 5),
                            );

                            builder.with_message(format!(
                                "struct literal does not have the fields{} {formatted_extra_fields}",
                                pluralise!(extra_fields.len())
                            ));

                            // Add note about what fields shouldn't be there
                            // @@Future: It would be nice to highlight the exact fields and just
                            // show them specifically rather than the whole subject expression...
                            if let Some(location) =
                                ctx.location_store().get_location(*args_location)
                            {
                                builder.add_element(ReportElement::CodeBlock(
                                    ReportCodeBlock::new(
                                        location,
                                        format!(
                                            "field{} {formatted_extra_fields} do not exist on this struct",
                                            pluralise!(extra_fields.len())
                                        ),
                                    ),
                                ));
                            }
                        }

                        // Provide information about the location of the target type if available
                        if let Some(location) = ctx.location_store().get_location(*params_location)
                        {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                "the struct is defined here",
                            )));
                        }
                    }
                    _ => {
                        // @@ErrorReporting: get more customised messages for other variant
                        // mismatch...
                        builder
                            .with_error_code(HashErrorCode::ParameterLengthMismatch)
                            .with_message(format!(
                                "{} expects {} arguments, however {} arguments were given",
                                params_origin,
                                params.len(),
                                args.len()
                            ));

                        // Provide information about the location of the target type if available
                        if let Some(location) = ctx.location_store().get_location(*args_location) {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("got {} arguments here...", args.len()),
                            )));
                        }

                        // Provide information about the location of the target type if available
                        if let Some(location) = ctx.location_store().get_location(*params_location)
                        {
                            builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                                location,
                                format!("...but this expects {} arguments.", args.len()),
                            )));
                        }
                    }
                }
            }
            TcError::ParamNotFound { args_kind, params_subject, name } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedNameInValue)
                    .with_message(format!("{} `{name}` is not defined", args_kind.as_noun()));

                // find the parameter and report the location
                let id = ctx.param_ops().get_name_by_index(args_kind, *name).unwrap();

                // Provide information about the location of the target type if available
                if let Some(location) = ctx.param_ops().field_location(args_kind, id) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("{} `{name}` not defined", args_kind.as_noun()),
                    )));
                }

                // Provide information about the location of the target type if available
                if let Some(location) = ctx.location_store().get_location(*params_subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("the {} is defined here", ctx.param_ops().origin(args_kind)),
                    )));
                }
            }
            TcError::ParamGivenTwice { param_kind, index } => {
                let origin = ctx.param_ops().origin(param_kind);

                // we want to get the particular argument at the specified index, get the name
                // and then later use the name to find the original use so that it can be
                // added to the report.
                //
                // Safety: this should be safe to unwrap otherwise we can't detect this issue.
                let (name, first_use) = match param_kind {
                    ParamListKind::Params(id) => {
                        let params = ctx.params_store().get_owned_param_list(*id);

                        // Extract the name from the parameter
                        let Param { name, .. } = params.positional()[*index];
                        let name = name.unwrap();

                        // find the index of the first name
                        let first_use = params
                            .positional()
                            .iter()
                            .position(|param| param.name == Some(name))
                            .unwrap();

                        (name, first_use)
                    }
                    ParamListKind::Args(id) => {
                        let args = ctx.args_store().get_owned_param_list(*id);

                        // Extract the name from the argument
                        let ArgOld { name, .. } = args.positional()[*index];
                        let name = name.unwrap();

                        // find the index of the first name
                        let first_use = args
                            .positional()
                            .iter()
                            .position(|param| param.name == Some(name))
                            .unwrap();

                        (name, first_use)
                    }
                    ParamListKind::PatArgs(id) => {
                        let args = ctx.pat_args_store().get_owned_param_list(*id);

                        // Extract the name from the argument
                        let PatArg { name, .. } = args.positional()[*index];
                        let name = name.unwrap();

                        // find the index of the first name
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
                if let Some(location) = ctx.param_ops().field_location(param_kind, *index) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("parameter `{name}` has already been used"),
                    )));
                }

                if let Some(location) = ctx.param_ops().field_location(param_kind, first_use) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "initial use occurs here",
                    )));
                }
            }
            TcError::AmbiguousArgumentOrdering { param_kind, index } => {
                let origin = ctx.param_ops().origin(param_kind);

                builder
                    .with_error_code(HashErrorCode::AmbiguousFieldOrder)
                    .with_message(format!("ambiguous parameter ordering within a {origin}"));

                // Add the location of the
                if let Some(location) = ctx.param_ops().field_location(param_kind, *index) {
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
                        value.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` does not contain the {} `{}`",
                            value.for_formatting(ctx.global_storage()),
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

                if let Some(location) = ctx.location_store().get_location(value) {
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

                if let Some(location) = ctx.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` cannot be accessed using with the name `{}`",
                            value.for_formatting(ctx.global_storage()),
                            name
                        ),
                    )));
                }
            }
            TcError::UnsupportedNamespaceAccess { name, value } => {
                builder.with_error_code(HashErrorCode::UnsupportedNamespaceAccess).with_message(
                    format!(
                        "unsupported namespace access, `{}` cannot be namespaced",
                        value.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "`{}` cannot be namespaced using with the name `{}`",
                            value.for_formatting(ctx.global_storage()),
                            name
                        ),
                    )));
                }
            }

            TcError::UnsupportedPropertyAccess { name, value } => {
                builder.with_error_code(HashErrorCode::UnsupportedPropertyAccess).with_message(
                    format!(
                        "unsupported property access for type `{}`",
                        value.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "the property `{}` cannot be accessed from `{}`, it does not support property accessing",
                            name,
                            value.for_formatting(ctx.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnApplication { type_fn, cases, unification_errors, .. } => {
                builder.with_error_code(HashErrorCode::TypeMismatch).with_message(format!(
                    "the type function `{}` cannot be applied",
                    type_fn.for_formatting(ctx.global_storage()),
                ));

                // Now we show where the unification shouldn't occur
                if let Some(location) = ctx.location_store().get_location(type_fn) {
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
                    .map(|error| TcErrorWithStorage::new(error.clone(), ctx.storages()).into())
                    .collect();

                // @@Todo(feds01): Now we need to merge the reports:
            }
            TcError::InvalidMergeElement { term } => {
                builder
                    .with_error_code(HashErrorCode::InvalidMergeElement)
                    .with_message("invalid element within a merge declaration");

                if let Some(location) = ctx.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within a merge declaration",
                            term.for_formatting(ctx.global_storage()),
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

                if let Some(location) = ctx.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within a union",
                            term.for_formatting(ctx.global_storage()),
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

                if let Some(location) = ctx.location_store().get_location(param_ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` within as the type of a function parameter",
                            param_ty.for_formatting(ctx.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnReturnTy { return_ty } => {
                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message("invalid function return type".to_string());

                if let Some(location) = ctx.location_store().get_location(return_ty) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "cannot use the type `{}` as the return type of a function",
                            return_ty.for_formatting(ctx.global_storage()),
                        ),
                    )));
                }
            }
            TcError::InvalidTyFnReturnValue { return_value } => {
                builder
                    .with_error_code(HashErrorCode::DisallowedType)
                    .with_message("invalid type of function return value".to_string());

                if let Some(location) = ctx.location_store().get_location(return_value) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this can't be used as the return of the function",
                    )));

                    // @@Todo(feds01): more information about why this is disallowed
                    builder.add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        format!(
                            "the type of the return value `{}` which is disallowed",
                            return_value.for_formatting(ctx.global_storage()),
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

                if let Some(location) = ctx.location_store().get_location(initial_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "the merge declaration has an initial nominal term here",
                    )));
                }

                if let Some(location) = ctx.location_store().get_location(offending_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "...and the second nominal term use occurs here",
                    )));
                }

                // Add the location of the actual merge for annotation
                if let Some(location) = ctx.location_store().get_location(merge_term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "within this merge term",
                    )));
                }
            }

            TcError::MergeShouldBeLevel1 { merge_term, offending_term } => {
                let location = ctx.location_store().get_location(merge_term).unwrap();

                let offender = ctx.term_store().get(*offending_term);
                let offender_location = ctx.location_store().get_location(offending_term).unwrap();

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
                            offender.get_term_level(ctx.term_store())
                        ),
                    )));
            }
            TcError::MergeShouldBeLevel2 { merge_term, offending_term } => {
                let location = ctx.location_store().get_location(merge_term).unwrap();

                let offender = ctx.term_store().get(*offending_term);
                let offender_location = ctx.location_store().get_location(offending_term).unwrap();

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
                            offender.get_term_level(ctx.term_store())
                        ),
                    )));
            }
            TcError::NeedMoreTypeAnnotationsToResolve { term } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedType)
                    .with_message("insufficient information to resolve types".to_string());

                if let Some(location) = ctx.location_store().get_location(term) {
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
                        term.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(term) {
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

                if let Some(location) = ctx.location_store().get_location(subject_id) {
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
                if let Some(location) = ctx.location_store().get_location(access.subject) {
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
                                result.for_formatting(ctx.global_storage())
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

                if let Some(location) = ctx.location_store().get_location(subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this is not a method",
                    )));
                }
            }
            TcError::UninitialisedMemberNotAllowed { member } => {
                builder
                    .with_error_code(HashErrorCode::UninitialisedMember)
                    .with_message("members must be initialised in the current scope");

                if let Some(location) = ctx.location_store().get_location(member) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this declaration must be initialised",
                    )));
                }
            }
            TcError::CannotImplementNonTrait { term } => {
                builder.with_error_code(HashErrorCode::TypeIsNotTrait).with_message(format!(
                    "type `{}` is not a trait",
                    term.for_formatting(ctx.global_storage())
                ));

                if let Some(location) = ctx.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this cannot be implemented because it's not a trait",
                    )));
                }
            }
            TcError::TraitImplMissingMember {
                trt_impl_term_id,
                trt_def_term_id,
                missing_trt_members,
            } => {
                let TrtDefOld { members, .. } =
                    ctx.oracle().term_as_trt_def(*trt_def_term_id).expect("trait def term");
                let trt_scope = ctx.reader().get_scope_copy(members);

                let missing = missing_trt_members
                    .iter()
                    .map(|index| trt_scope.get_by_index(*index).name())
                    .collect_vec();

                // Create a sequence display for displaying member names
                let missing_members = SequenceDisplay::new(
                    &missing,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 6),
                );

                builder.with_error_code(HashErrorCode::TraitImplMissingMember).with_message(
                    format!(
                        "trait `{}` is missing the member{} {missing_members}",
                        trt_def_term_id.for_formatting(ctx.global_storage()),
                        pluralise!(missing_trt_members.len())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(trt_impl_term_id) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("implementation is missing {missing_members}",),
                    )));
                }

                // Add the location of the missing member definition if possible
                for missing_member_index in missing_trt_members.iter().copied() {
                    if let Some(location) =
                        ctx.location_store().get_location((members, missing_member_index))
                    {
                        let name = trt_scope.get_by_index(missing_member_index).name();

                        builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                            location,
                            format!("trait item `{name}` is defined here",),
                        )));
                    }
                }
            }
            TcError::MethodNotAMemberOfTrait { trt_def_term_id, member, name } => {
                builder.with_error_code(HashErrorCode::MethodNotAMemberOfTrait).with_message(
                    format!(
                        "method `{name}` is not a member of trait `{}`",
                        trt_def_term_id.for_formatting_with_opts(
                            ctx.global_storage(),
                            TcFormatOpts { expand: false }
                        ),
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(member) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "not a member of trait `{}`",
                            trt_def_term_id.for_formatting_with_opts(
                                ctx.global_storage(),
                                TcFormatOpts { expand: false }
                            ),
                        ),
                    )));
                }
            }
            TcError::InvalidCallSubject { term } => {
                // @@Todo: error code
                builder.with_message(format!(
                    "cannot use `{}` as a function call subject",
                    term.for_formatting(ctx.global_storage())
                ));

                if let Some(location) = ctx.location_store().get_location(term) {
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

                if let Some(location) = ctx.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "pattern `{}` is given here on an unset declaration",
                            pat.for_formatting(ctx.global_storage())
                        ),
                    )));
                }
            }
            TcError::InvalidAssignSubject { location } => {
                builder.with_error_code(HashErrorCode::InvalidAssignSubject).with_message(
                    "assignment left-hand side needs to be a stack variable".to_string(),
                );

                if let Some(location) = ctx.location_store().get_location(*location) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "non-variable term given in an assignment here",
                    )));
                }
            }
            TcError::NoConstructorOnType { subject } => {
                builder.with_message(format!(
                    "type `{}` has no instantiable constructor",
                    subject.for_formatting(ctx.global_storage())
                ));

                if let Some(location) = ctx.location_store().get_location(subject) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::NoCallableConstructorOnType { subject } => {
                builder.with_message(format!(
                    "type `{}` has a constant constructor, not a callable one",
                    subject.for_formatting(ctx.global_storage())
                ));

                if let Some(location) = ctx.location_store().get_location(subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "try to remove the argument list here",
                    )));
                }
            }
            TcError::IdentifierBoundMultipleTimes { name, pat } => {
                builder.with_error_code(HashErrorCode::IdentifierBoundMultipleTimes).with_message(
                    format!("identifier `{name}` is bound multiple times in the same pattern"),
                );

                if let Some(location) = ctx.location_store().get_location(pat) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::MissingPatternBounds { pat, bounds } => {
                builder.with_error_code(HashErrorCode::MissingPatternBounds).with_message(format!(
                    "variables {} are not declared in all patterns",
                    SequenceDisplay::all(bounds.as_slice())
                ));

                if let Some(location) = ctx.location_store().get_location(pat) {
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
                    .map(|id| format!("{}", id.for_formatting(ctx.global_storage())))
                    .collect_vec();

                let pats = SequenceDisplay::new(
                    &uncovered,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 3),
                );

                builder.with_error_code(HashErrorCode::RefutablePat).with_message(format!(
                    "refutable pattern in {origin} binding: {pats} not covered",
                ));

                if let Some(location) = ctx.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("pattern{} {pats} not covered", pluralise!(uncovered.len())),
                    )));
                }
            }
            TcError::NonExhaustiveMatch { term, uncovered_pats } => {
                let uncovered = uncovered_pats
                    .iter()
                    .map(|id| format!("{}", id.for_formatting(ctx.global_storage())))
                    .collect_vec();

                let pats = SequenceDisplay::new(
                    &uncovered,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 3),
                );

                builder
                    .with_error_code(HashErrorCode::NonExhaustiveMatch)
                    .with_message(format!("non-exhaustive patterns: {pats} not covered"));

                if let Some(location) = ctx.location_store().get_location(term) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("pattern{} {pats} not covered", pluralise!(uncovered.len())),
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

                if let Some(location) = ctx.location_store().get_location(term) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcError::UnsupportedRangePatTy { term } => {
                builder.with_error_code(HashErrorCode::InvalidRangePatBoundaries).with_message(
                    format!(
                        "the type `{}` is not supported in range patterns",
                        term.for_formatting(ctx.global_storage())
                    ),
                );

                if let Some(location) = ctx.location_store().get_location(term) {
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
            TcError::MemberIsImmutable { name, site, decl } => {
                builder
                    .with_error_code(HashErrorCode::ItemIsImmutable)
                    .with_message(format!("cannot assign twice to immutable variable `{name}`"));

                if let Some(location) = ctx.location_store().get_location(decl) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                            location,
                            format!("first assignment to `{name}`"),
                        )))
                        .add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Help,
                            format!("consider declaring this variable as mutable: `mut {name}`"),
                        )));
                }

                if let Some(location) = ctx.location_store().get_location(site) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "cannot assign twice to immutable variable",
                    )));
                }
            }
            TcError::MemberMustBeImmutable { name, site } => {
                builder.with_error_code(HashErrorCode::ItemMustBeImmutable).with_message(format!(
                    "`{name}` must be declared as immutable in a constant scope"
                ));

                if let Some(location) = ctx.location_store().get_location(site) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "this member cannot be declared as mutable: remove `mut`",
                    )));
                }
            }
        };

        builder.build()
    }
}
