//! Definitions related to arguments to data structures, functions,
//! etc.

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};

use super::{params::ParamTarget, pats::PatId};
use crate::new::terms::TermId;

/// An argument to a parameter.
///
/// This might be used for arguments in constructor calls `C(...)`, function
/// calls `f(...)` or `f<...>`, or type arguments.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Arg {
    /// The ID of the argument in the argument list.
    pub id: ArgId,
    /// Argument target (named or positional).
    pub target: ParamTarget,
    /// The term that is the value of the argument.
    pub value: TermId,
}

new_sequence_store_key!(pub ArgsId);
pub type ArgId = (ArgsId, usize);
pub type ArgsStore = DefaultSequenceStore<ArgsId, Arg>;

/// A pattern argument to a parameter
///
/// This might be used for constructor patterns like `C(true, x)`.
#[derive(Clone, Debug, Copy)]
pub struct PatArg {
    /// The ID of the argument in the argument pattern list.
    pub id: PatArgId,
    /// Argument target (named or positional).
    pub target: ParamTarget,
    /// The pattern in place for this argument.
    pub pat: PatId,
}

new_sequence_store_key!(pub PatArgsId);
pub type PatArgId = (PatArgsId, usize);
pub type PatArgsStore = DefaultSequenceStore<PatArgsId, PatArg>;
