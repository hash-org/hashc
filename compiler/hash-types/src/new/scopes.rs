//! Definitions related to stack scopes, and variable declarations.

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};

use crate::new::{
    pats::PatId,
    symbols::Symbol,
    terms::{TermId, TermListId},
    types::TyId,
};

/// Term to declare new variable(s) in the current stack scope.
///
/// Depending on the `bind_pat` used, this can be used to declare a single or
/// multiple variables.
#[derive(Debug, Clone, Copy)]
pub struct DeclStackMemberTerm {
    pub is_mutable: bool,
    pub bind_pat: PatId,
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// Term to assign a value to a subject.
///
/// @@Todo: figure out exact rules about what subject could be.
#[derive(Debug, Clone, Copy)]
pub struct AssignTerm {
    pub subject: TermId,
    pub value: TermId,
}

/// The kind of an access.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AccessKind {
    Numeric(usize),
    Named(Symbol),
}

/// Term to access a nested value.
#[derive(Debug, Clone, Copy)]
pub struct AccessTerm {
    pub subject: TermId,
    pub access_kind: AccessKind,
}

/// A variable on the stack.
#[derive(Debug, Copy, Clone)]
pub struct StackMember {
    pub is_mutable: bool,
    pub name: Symbol,
    pub original_stack_scope_id: StackScopeId,
    pub index: usize,
    pub ty: TyId,
    pub value: Option<TermId>,
}
new_sequence_store_key!(pub StackScopeId);
pub type StackScopeStore = DefaultSequenceStore<StackScopeId, StackMember>;
pub type StackMemberId = (StackScopeId, usize);

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub statements: TermListId,
    pub return_value: TermId,
}
