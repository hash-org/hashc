//! Error-related data structures for errors that occur during typechecking.
use crate::storage::primitives::{Args, Params, TyId, ValueId};
use hash_source::identifier::Identifier;

/// Convenient type alias for a result with a [TcError] as the error type.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
///
/// @@Incomplete: more variants will be added here (most likely copied over from the old version)
/// once more of the typechecker is implemented.
#[derive(Debug, Clone)]
pub enum TcError {
    /// Cannot unify the two types, where the first is the source and the second is the target.
    CannotUnify(TyId, TyId),
    NotATypeFunction(ValueId),
    CannotUseValueAsTy(ValueId),
    CannotUsePositionalArgAfterNamedArg(Args, usize),
    MismatchingArgParamLength(Args, Params),
    ParamNotFound(Params, Identifier),
    ParamGivenTwice(Args, Params, usize),
    UnresolvedSymbol(Identifier),
    TryingToNamespaceValue(ValueId),
}
