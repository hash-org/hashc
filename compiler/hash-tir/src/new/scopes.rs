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

use super::{
    environment::env::{AccessToEnv, WithEnv},
    pats::Pat,
    terms::Term,
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

/// Indices into a stack, that represent a contiguous range of stack members.
#[derive(Debug, Clone, Copy)]
pub enum StackIndices {
    Empty,
    Range { start: usize, end: usize },
}

impl StackIndices {
    pub fn as_option(&self) -> Option<(usize, usize)> {
        match self {
            StackIndices::Empty => None,
            StackIndices::Range { start, end } => Some((*start, *end)),
        }
    }

    /// Add a new index to the range.
    pub fn extend_with_index(&mut self, index: usize) {
        match self {
            StackIndices::Empty => *self = StackIndices::Range { start: index, end: index },
            StackIndices::Range { start, end } => {
                if index < *start {
                    *start = index;
                } else if index > *end {
                    *end = index;
                }
            }
        }
    }
}

/// Term to declare new variable(s) in the current stack scope.
///
/// Also contains the stack indices of the declared variables in the `bind_pat`.
///
/// Depending on the `bind_pat` used, this can be used to declare a single or
/// multiple variables.
#[derive(Debug, Clone, Copy)]
pub struct DeclTerm {
    pub bind_pat: PatId,
    pub stack_indices: StackIndices,
    pub ty: TyId,
    pub value: Option<TermId>,
}

impl DeclTerm {
    /// Returns the range of stack indices that this declaration covers.
    pub fn iter_stack_indices(&self) -> impl Iterator<Item = usize> {
        self.stack_indices.as_option().map(|s| s.0..=s.1).into_iter().flatten()
    }
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
    pub stack_id: StackId, // The associated stack ID for this block.
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

impl fmt::Display for WithEnv<'_, &DeclTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = match self.value.value {
            Some(term_id) => self.stores().pat().map_fast(self.value.bind_pat, |pat| match pat {
                Pat::Binding(binding_pat) => {
                    self.stores().term().map_fast(term_id, |term| {
                        match term {
                            // If a function is being declared, print the body, otherwise just its
                            // name.
                            Term::FnRef(fn_def_id)
                                if self.stores().fn_def().map_fast(*fn_def_id, |fn_def| {
                                    fn_def.name == binding_pat.name
                                }) =>
                            {
                                self.env().with(*fn_def_id).to_string()
                            }
                            _ => self.env().with(term_id).to_string(),
                        }
                    })
                }
                _ => self.env().with(term_id).to_string(),
            }),
            None => "{uninitialised}".to_string(),
        };

        write!(
            f,
            "{}: {} = {}",
            self.env().with(self.value.bind_pat),
            self.env().with(self.value.ty),
            value,
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
                writeln!(f, "{};", indent(&term, "  "))?;
            }
            Ok(())
        })?;
        let return_value = self.env().with(self.value.return_value).to_string();
        write!(f, "{}", indent(&return_value, "  "))?;
        write!(f, "\n}}")
    }
}
