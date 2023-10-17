//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use core::fmt;

use hash_storage::{
    get,
    store::statics::{SingleStoreId, StoreId},
};
use hash_utils::parking_lot::{MappedRwLockReadGuard, MappedRwLockWriteGuard};
use textwrap::indent;
use utility_types::omit;

use crate::{
    context::ContextMember,
    stores::tir_stores,
    tir::{ModDefId, Node, NodeOrigin, SymbolId, TyId},
    tir_node_single_store,
};

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

/// A variable on the stack.
#[omit(StackMemberData, [id], [Debug, Copy, Clone])]
#[derive(Debug, Copy, Clone)]
pub struct StackMember {
    pub name: SymbolId,
    pub is_mutable: bool,
    pub ty: TyId,
}

/// A stack, which is a list of stack members.
#[derive(Debug, Clone)]
pub struct Stack {
    pub members: Vec<ContextMember>,
    /// Local module definition containing members that are defined in this
    /// stack.
    pub local_mod_def: Option<ModDefId>,
}

impl Stack {
    /// Create a new stack with empty members.
    pub fn empty(origin: NodeOrigin) -> StackId {
        Node::create_at(Stack { members: vec![], local_mod_def: None }, origin)
    }
}

tir_node_single_store!(Stack);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StackMemberId(pub StackId, pub usize);

impl SingleStoreId for StackMemberId {}
impl StoreId for StackMemberId {
    type Value = ContextMember;
    type ValueRef = ContextMember;
    type ValueBorrow = MappedRwLockReadGuard<'static, ContextMember>;
    type ValueBorrowMut = MappedRwLockWriteGuard<'static, ContextMember>;

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
            self.local_mod_def.map(|mod_def_id| get!(mod_def_id, members))
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
        write!(f, "{}", *self.value())
    }
}
