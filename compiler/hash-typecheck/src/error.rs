//! Error-related data structures for errors that occur during typechecking.
use crate::storage::primitives::{AccessTerm, Args, Params, TermId};
use hash_source::identifier::Identifier;

/// Convenient type alias for a result with a [TcError] as the error type.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
///
/// @@Incomplete: more variants will be added here (most likely copied over from the old version)
/// once more of the typechecker is implemented.
#[derive(Debug, Clone)]
pub enum TcError {
    /// Cannot unify the two terms, where the first is the source and the second is the target.
    CannotUnify {
        src: TermId,
        target: TermId,
    },
    CannotUnifyParams {
        src_params: Params,
        target_params: Params,
    },
    NotATypeFunction {
        term: TermId,
    },
    CannotUseValueAsTy {
        value: TermId,
    },
    MismatchingArgParamLength {
        args: Args,
        params: Params,
    },
    ParamNotFound {
        field1: Params,
        field2: Identifier,
    },
    ParamGivenTwice {
        args: Args,
        params: Params,
        param_index_given_twice: usize,
    },
    CannotUsePositionalArgAfterNamedArg {
        args: Args,
        problematic_arg_index: usize,
    },
    UnresolvedNameInValue {
        name: Identifier,
        value: TermId,
    },
    UnresolvedVariable {
        name: Identifier,
    },
    UnsupportedAccess {
        name: Identifier,
        value: TermId,
    },
    UnsupportedNamespaceAccess {
        name: Identifier,
        value: TermId,
    },
    UnsupportedPropertyAccess {
        name: Identifier,
        value: TermId,
    },
    InvalidTypeFunctionApplication {
        type_fn: TermId,
        args: Args,
        unification_errors: Vec<TcError>,
    },
    InvalidElementOfMerge {
        term: TermId,
    },
    InvalidTypeFunctionParameterType {
        param_ty: TermId,
    },
    InvalidTypeFunctionReturnType {
        return_ty: TermId,
    },
    InvalidTypeFunctionReturnValue {
        return_value: TermId,
    },
    MergeShouldOnlyContainOneNominal {
        merge_term: TermId,
        nominal_term: TermId,
        second_nominal_term: TermId,
    },
    MergeShouldBeLevel1 {
        merge_term: TermId,
        offending_term: TermId,
    },
    NeedMoreTypeAnnotationsToResolve {
        term_to_resolve: TermId,
    },
    MergeShouldBeLevel2 {
        merge_term: TermId,
        offending_term: TermId,
    },
    TermIsNotRuntimeInstantiable {
        term: TermId,
    },
    UnsupportedTypeFunctionApplication {
        subject_id: TermId,
    },
    AmbiguousAccess {
        access: AccessTerm,
    },
    InvalidPropertyAccessOfNonMethod {
        subject: TermId,
        property: Identifier,
    },
}
