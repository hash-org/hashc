//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use core::fmt;

use hash_utils::{new_store_key, store::DefaultStore};
use utility_types::omit;

use super::environment::env::WithEnv;
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

/// A stack, which is a list of stack members.
#[derive(Debug, Clone)]
#[omit(StackData, [id], [Debug, Clone])]
pub struct Stack {
    pub id: StackId,
    pub members: Vec<StackMember>,
}

new_store_key!(pub StackId);
pub type StackStore = DefaultStore<StackId, Stack>;
pub type StackMemberId = (StackId, usize);

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub statements: TermListId,
    pub return_value: TermId,
}

impl fmt::Display for WithEnv<'_, StackMemberId> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl fmt::Display for WithEnv<'_, &StackMember> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
