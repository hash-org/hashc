//! Error-related data structures for errors that occur during typechecking.
use crate::storage::primitives::{AccessTerm, Args, Params, TermId};
use hash_source::identifier::Identifier;

/// Convenient type alias for a result with a [TcError] as the error type.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
#[derive(Debug, Clone)]
pub enum TcError {
    /// Cannot unify the two terms.
    CannotUnify { src: TermId, target: TermId },
    /// Cannot unify the two parameter lists.
    CannotUnifyParams {
        src_params: Params,
        target_params: Params,
    },
    /// The given term should be a type function but it isn't.
    NotATypeFunction { term: TermId },
    /// The given value cannot be used as a type.
    CannotUseValueAsTy { value: TermId },
    /// The given arguments do not match the length of the target parameters.
    MismatchingArgParamLength { args: Args, params: Params },
    /// The parameter with the given name is not found in the given parameter
    /// list.
    ParamNotFound { params: Params, name: Identifier },
    /// There is a parameter (at the index `param_index_given_twice`) which is
    /// specified twice in the given argument list.
    ParamGivenTwice {
        args: Args,
        params: Params,
        param_index_given_twice: usize,
    },
    /// It is invalid to use a positional argument after a named argument.
    CannotUsePositionalArgAfterNamedArg {
        args: Args,
        problematic_arg_index: usize,
    },
    /// The given name cannot be resolved in the given value.
    UnresolvedNameInValue { name: Identifier, value: TermId },
    /// The given variable cannot be resolved in the current context.
    UnresolvedVariable { name: Identifier },
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
        args: Args,
        unification_errors: Vec<TcError>,
    },
    /// The given term cannot be used in a merge operation.
    InvalidElementOfMerge { term: TermId },
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
        nominal_term: TermId,
        second_nominal_term: TermId,
    },
    /// The given merge term should contain only level 1 terms.
    MergeShouldBeLevel1 {
        merge_term: TermId,
        offending_term: TermId,
    },
    /// The given merge term should contain only level 2 terms.
    MergeShouldBeLevel2 {
        merge_term: TermId,
        offending_term: TermId,
    },
    /// More type annotations are needed to resolve the given term.
    NeedMoreTypeAnnotationsToResolve { term_to_resolve: TermId },
    /// The given term cannot be instantiated at runtime.
    TermIsNotRuntimeInstantiable { term: TermId },
    /// The given term cannot be used as the subject of a type function
    /// application.
    UnsupportedTypeFunctionApplication { subject_id: TermId },
    /// The given access operation results in more than one result.
    AmbiguousAccess { access: AccessTerm },
    /// The given access operation does not resolve to a method.
    InvalidPropertyAccessOfNonMethod {
        subject: TermId,
        property: Identifier,
    },
}
