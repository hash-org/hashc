//! Definitions related to arguments to data structures, functions,
//! etc.

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};

use crate::new::{symbols::Symbol, terms::TermId};

/// An argument to a parameter.
///
/// This might be used for arguments in constructor calls `C(...)`, function
/// calls `f(...)` or `f<...>`, or type arguments.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Arg {
    /// Optional name that is attached to the argument.
    pub name: Option<Symbol>,
    /// The term that is the value of the argument.
    pub value: TermId,
}

new_sequence_store_key!(pub ArgsId);
pub type ArgsStore = DefaultSequenceStore<ArgsId, Arg>;
