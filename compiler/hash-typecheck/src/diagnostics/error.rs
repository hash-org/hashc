//! Error-related data structures for errors that occur during typechecking.

use crate::storage::primitives::{AccessTerm, ArgsId, ParamsId, TermId, TyFnCase};
use hash_source::identifier::Identifier;

use super::{
    params::{ParamListKind, ParamUnificationErrorReason},
    symbol::NameFieldOrigin,
};

/// Convenient type alias for a result with a [TcError] as the error type.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
#[derive(Debug, Clone)]
pub enum TcError {
    /// Cannot unify the two terms.
    CannotUnify { src: TermId, target: TermId },
    /// Cannot unify the two parameter lists. This can occur if the names
    /// don't match of the parameters or if the number of parameters isn't the
    /// same.
    CannotUnifyParams {
        src_params_id: ParamsId,
        target_params_id: ParamsId,
        src: TermId,
        target: TermId,
        reason: ParamUnificationErrorReason,
    },
    /// The given term should be a type function but it isn't.
    NotATypeFunction { term: TermId },
    /// The given value cannot be used as a type.
    CannotUseValueAsTy { value: TermId },
    /// The given arguments do not match the length of the target parameters.
    MismatchingArgParamLength { args: ArgsId, params: ParamsId, target: TermId },
    /// The parameter with the given name is not found in the given parameter
    /// list.
    ParamNotFound { params: ParamsId, name: Identifier },
    /// There is a argument or parameter (at the index) which is
    /// specified twice in the given argument list.
    ParamGivenTwice { param_kind: ParamListKind, index: usize },
    /// It is invalid to use a positional argument after a named argument.
    AmbiguousArgumentOrdering { param_kind: ParamListKind, index: usize },
    /// The given name cannot be resolved in the given value.
    UnresolvedNameInValue { name: Identifier, origin: NameFieldOrigin, value: TermId },
    /// The given variable cannot be resolved in the current context.
    UnresolvedVariable { name: Identifier, value: TermId },
    /// The given value does not support accessing (of the given name).
    UnsupportedAccess { name: Identifier, value: TermId },
    /// The given value does not support namespace accessing (of the given
    /// name).
    UnsupportedNamespaceAccess { name: Identifier, value: TermId },
    /// The given value does not support property accessing (of the given name).
    UnsupportedPropertyAccess { name: Identifier, value: TermId },
    /// The given type function cannot be applied to the given arguments, due to
    /// the given errors.
    InvalidTypeFunctionApplication {
        type_fn: TermId,
        cases: Vec<TyFnCase>,
        args: ArgsId,
        unification_errors: Vec<TcError>,
    },
    /// The given term cannot be used in a merge operation.
    InvalidMergeElement { term: TermId },
    /// The given term cannot be used in a union operation.
    InvalidUnionElement { term: TermId },
    /// The given term cannot be used as a type function parameter type.
    InvalidTypeFunctionParameterType { param_ty: TermId },
    /// The given term cannot be used as a type function return type.
    InvalidTypeFunctionReturnType { return_ty: TermId },
    /// The given term cannot be used as a type function return value.
    InvalidTypeFunctionReturnValue { return_value: TermId },
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
    UnsupportedTypeFunctionApplication { subject_id: TermId },
    /// The given access operation results in more than one result.
    AmbiguousAccess { access: AccessTerm, results: Vec<TermId> },
    /// Cannot use this as a function call subject.
    InvalidFunctionCallSubject { term: TermId },
    /// The given access operation does not resolve to a method.
    InvalidPropertyAccessOfNonMethod { subject: TermId, property: Identifier },
    /// The given member requires an initialisation in the current scope.
    /// @@ErrorReporting: add span of member.
    UninitialisedMemberNotAllowed { member_ty: TermId },
    /// Cannot implement something that isn't a trait.
    CannotImplementNonTrait { term: TermId },
    /// The trait implementation `trt_impl_term_id` is missing the member
    /// `trt_def_missing_member_id` from the trait `trt_def_term_id`.
    ///
    /// @@ErrorReporting: identify all missing members
    TraitImplMissingMember {
        trt_impl_term_id: TermId,
        trt_def_term_id: TermId,
        // @@ErrorReporting: Ideally we want to be able to identify whole members rather than just
        // "terms".
        trt_def_missing_member_term_id: TermId,
    },
}
