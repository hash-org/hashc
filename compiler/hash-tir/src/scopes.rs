//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use core::fmt;

use hash_storage::{
    static_single_store,
    store::{
        statics::{SingleStoreValue, StoreId},
        TrivialSequenceStoreKey,
    },
};
use hash_utils::parking_lot::{MappedRwLockReadGuard, MappedRwLockWriteGuard};
use textwrap::indent;
use utility_types::omit;

use super::{pats::Pat, terms::Term};
use crate::{
    context::Decl,
    environment::stores::tir_stores,
    mods::ModDefId,
    pats::PatId,
    symbols::Symbol,
    terms::{TermId, TermListId},
    tir_get,
    tys::TyId,
};

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
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
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// Term to assign a value to a subject.
#[derive(Debug, Clone, Copy)]
pub struct AssignTerm {
    // If the subject is assign,
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
}

/// A stack, which is a list of stack members.
#[derive(Debug, Clone)]
#[omit(StackData, [id], [Debug, Clone])]
pub struct Stack {
    pub id: StackId,
    pub members: Vec<Decl>,
    /// Local module definition containing members that are defined in this
    /// stack.
    pub local_mod_def: Option<ModDefId>,
}

impl Stack {
    /// Create a new stack with empty members.
    pub fn empty() -> StackId {
        Stack::create_with(|id| Stack { id, members: vec![], local_mod_def: None })
    }
}

static_single_store!(
    store = pub StackStore,
    id = pub StackId,
    value = Stack,
    store_name = stack,
    store_source = tir_stores(),
    derives = Debug
);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StackMemberId(pub StackId, pub usize);

impl StoreId for StackMemberId {
    type Value = Decl;
    type ValueRef = Decl;
    type ValueBorrow = MappedRwLockReadGuard<'static, Decl>;
    type ValueBorrowMut = MappedRwLockWriteGuard<'static, Decl>;

    fn borrow(self) -> Self::ValueBorrow {
        MappedRwLockReadGuard::map(self.0.borrow(), |stack| &stack.members[self.1])
    }

    fn borrow_mut(self) -> Self::ValueBorrowMut {
        MappedRwLockWriteGuard::map(self.0.borrow_mut(), |stack| &mut stack.members[self.1])
    }

    fn value(self) -> Self::Value {
        self.0.map(|stack| stack.members[self.1])
    }

    fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
        self.0.map(|stack| f(&stack.members[self.1]))
    }

    fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
        self.0.modify(|stack| f(&mut stack.members[self.1]))
    }

    fn set(self, value: Self::Value) {
        self.0.modify(|stack| stack.members[self.1] = value)
    }
}

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub stack_id: StackId, // The associated stack ID for this block.
    pub statements: TermListId,
    pub return_value: TermId,
}

impl fmt::Display for BindingPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.is_mutable { "mut " } else { "" }, self.name)
    }
}

impl fmt::Display for DeclTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = match self.value {
            Some(term_id) => {
                match *self.bind_pat.value() {
                    Pat::Binding(binding_pat) => {
                        match *term_id.value() {
                            // If a function is being declared, print the body, otherwise just
                            // its name.
                            Term::FnRef(fn_def_id)
                                if fn_def_id.map(|def| def.name == binding_pat.name) =>
                            {
                                fn_def_id.to_string()
                            }
                            _ => term_id.to_string(),
                        }
                    }
                    _ => term_id.to_string(),
                }
            }
            None => "{uninitialised}".to_string(),
        };

        write!(f, "{}: {} = {}", self.bind_pat, self.ty, value,)
    }
}

impl fmt::Display for AssignTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.subject, self.value)
    }
}

impl fmt::Display for StackMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}: {}", if self.is_mutable { "mut " } else { "" }, self.name, self.ty)
    }
}

impl fmt::Display for StackMemberId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;

        if let Some(mod_def_members) =
            self.local_mod_def.map(|mod_def_id| tir_get!(mod_def_id, members))
        {
            let members = (mod_def_members).to_string();
            write!(f, "{}", indent(&members, "  "))?;
        }

        for member in self.members.iter() {
            let member = (*member).to_string();
            write!(f, "{}", indent(&member, "  "))?;
        }

        write!(f, "}}")
    }
}

impl fmt::Display for StackId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for BlockTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;

        let stack_local_mod_def = tir_get!(self.stack_id, local_mod_def);
        if let Some(mod_def_members) =
            stack_local_mod_def.map(|mod_def_id| tir_get!(mod_def_id, members))
        {
            let members = mod_def_members.to_string();
            write!(f, "{}", indent(&members, "  "))?;
        }

        for term in self.statements.value().iter() {
            let term = term.to_string();
            writeln!(f, "{};", indent(&term, "  "))?;
        }

        let return_value = (self.return_value).to_string();
        writeln!(f, "{}", indent(&return_value, "  "))?;

        write!(f, "}}")
    }
}
