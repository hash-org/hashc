//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use core::fmt;

use hash_utils::{
    new_store_key,
    store::{DefaultStore, SequenceStore, Store},
};
use textwrap::indent;
use utility_types::omit;

use super::environment::{
    context::BoundVarOrigin,
    env::{AccessToEnv, WithEnv},
};
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

/// A bound variable, containing a name and an origin.
#[derive(Debug, Copy, Clone)]
pub struct BoundVar {
    pub name: Symbol,
    pub origin: BoundVarOrigin,
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

impl fmt::Display for WithEnv<'_, &BindingPat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            if self.value.is_mutable { "mut " } else { "" },
            self.env().with(self.value.name),
        )
    }
}

impl fmt::Display for WithEnv<'_, &DeclStackMemberTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} = {}",
            self.env().with(self.value.bind_pat),
            self.env().with(self.value.ty),
            self.value
                .value
                .map(|val| self.env().with(val).to_string())
                .unwrap_or_else(|| "{uninitialised}".to_string()),
        )
    }
}

impl fmt::Display for WithEnv<'_, &AssignTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.env().with(self.value.subject), self.env().with(self.value.value),)
    }
}

impl fmt::Display for WithEnv<'_, &StackMember> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}: {} = {}",
            if self.value.is_mutable { "mut " } else { "" },
            self.env().with(self.value.name),
            self.env().with(self.value.ty),
            self.value
                .value
                .map(|val| self.env().with(val).to_string())
                .unwrap_or_else(|| "{uninitialised}".to_string()),
        )
    }
}

impl fmt::Display for WithEnv<'_, StackMemberId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().stack().map_fast(self.value.0, |stack| {
            write!(f, "{}", self.env().with(&stack.members[self.value.1]))
        })
    }
}

impl fmt::Display for WithEnv<'_, &Stack> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for member in self.value.members.iter() {
            let member = self.env().with(member).to_string();
            write!(f, "{}", indent(&member, "  "))?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for WithEnv<'_, StackId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().stack().map_fast(self.value, |stack| write!(f, "{}", self.env().with(stack)))
    }
}

impl fmt::Display for WithEnv<'_, &BlockTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        self.stores().term_list().map_fast(self.value.statements, |list| {
            for term in list {
                let term = self.env().with(*term).to_string();
                write!(f, "{}", indent(&term, "  "))?;
            }
            Ok(())
        })?;
        let return_value = self.env().with(self.value.return_value).to_string();
        write!(f, "{}", indent(&return_value, "  "))?;
        write!(f, "}}")
    }
}
