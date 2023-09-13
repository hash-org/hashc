//! Definitions related to stack scopes, and variable declarations.
//!
//! This defines the stack scopes themselves, as well as declarations, accesses,
//! and assignments of variables.

use core::fmt;

use hash_storage::{
    get,
    store::{
        statics::{SingleStoreId, StoreId},
        TrivialSequenceStoreKey,
    },
};
use hash_utils::parking_lot::{MappedRwLockReadGuard, MappedRwLockWriteGuard};
use textwrap::indent;
use utility_types::omit;

use super::{pats::Pat, terms::Term};
use crate::{
    context::ContextMember,
    mods::ModDefId,
    node::{Node, NodeOrigin},
    pats::PatId,
    stores::tir_stores,
    symbols::SymbolId,
    terms::{TermId, TyId},
    tir_node_sequence_store_direct, tir_node_single_store,
};

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub struct BindingPat {
    /// The name of the bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the pattern is actually a wildcard `_`.
    pub name: SymbolId,
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
pub struct Decl {
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

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub stack_id: StackId, // The associated stack ID for this block.
    pub statements: BlockStatementsId,
    pub expr: TermId,
}

/// A statement in a block.
///
/// This is either an expression, or a declaration.
#[derive(Debug, Clone, Copy)]
pub enum BlockStatement {
    Decl(Decl),
    Expr(TermId),
}

tir_node_sequence_store_direct!(BlockStatement);

impl fmt::Display for BindingPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.is_mutable { "mut " } else { "" }, self.name)
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = match self.value {
            Some(term_id) => {
                match *self.bind_pat.value() {
                    Pat::Binding(binding_pat) => {
                        match *term_id.value() {
                            // If a function is being declared, print the body, otherwise just
                            // its name.
                            Term::Fn(fn_def_id)
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

impl fmt::Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockStatement::Decl(d) => {
                write!(f, "{}", d)
            }
            BlockStatement::Expr(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

impl fmt::Display for BlockStatementId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for BlockStatementsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for term in self.iter() {
            writeln!(f, "{};", term)?;
        }
        Ok(())
    }
}

impl fmt::Display for BlockTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;

        let stack_local_mod_def = get!(self.stack_id, local_mod_def);
        if let Some(mod_def_members) =
            stack_local_mod_def.map(|mod_def_id| get!(mod_def_id, members))
        {
            let members = mod_def_members.to_string();
            write!(f, "{}", indent(&members, "  "))?;
        }

        write!(f, "{}", indent(&self.statements.to_string(), "  "))?;
        writeln!(f, "{}", indent(&self.expr.to_string(), "  "))?;

        write!(f, "}}")
    }
}
