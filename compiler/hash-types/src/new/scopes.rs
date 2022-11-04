//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};
use utility_types::omit;

use crate::new::{
    pats::PatId,
    symbols::Symbol,
    terms::{TermId, TermListId},
    tys::TyId,
};

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy)]
pub struct BindingPat {
    /// The name of the bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the pattern is actually a wildcard `_`.
    pub name: Symbol,
    /// Whether the binding is declared as mutable.
    pub is_mutable: bool,
}

// @@Todo: examples

/// Term to declare new variable(s) in the current stack scope.
///
/// Depending on the `bind_pat` used, this can be used to declare a single or
/// multiple variables.
#[derive(Debug, Clone, Copy)]
pub struct DeclStackMemberTerm {
    pub bind_pat: PatId,
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// Term to assign a value to a subject.
// @@Todo: figure out exact rules about what subject could be.
#[derive(Debug, Clone, Copy)]
pub struct AssignTerm {
    pub subject: TermId,
    pub value: TermId,
}

/// A variable on the stack.
#[omit(StackMemberData, [id], [Debug, Copy, Clone])]
#[derive(Debug, Copy, Clone)]
pub struct StackMember {
    pub id: StackMemberId,
    pub name: Symbol,
    pub is_mutable: bool,
    pub ty: TyId,
    pub value: Option<TermId>,
}
new_sequence_store_key!(pub StackId);
pub type StackStore = DefaultSequenceStore<StackId, StackMember>;
pub type StackMemberId = (StackId, usize);

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub statements: TermListId,
    pub return_value: TermId,
}
