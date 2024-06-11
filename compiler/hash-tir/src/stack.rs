//! Definitions related to stack scopes.

use core::fmt;

use hash_storage::{get, store::statics::StoreId};
use textwrap::indent;

use crate::{
    stores::tir_stores,
    tir::{ModDefId, Node, NodeOrigin, SymbolId, TermId, TyId},
    tir_node_single_store,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StackMember {
    pub name: SymbolId,
    pub ty: Option<TyId>,
    pub value: Option<TermId>,
}

/// A stack, which is a list of stack members.
#[derive(Debug, Clone)]
pub struct Stack {
    pub members: Vec<StackMember>,
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

impl fmt::Display for StackMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.ty, self.value) {
            (Some(ty), Some(value)) => write!(f, "{}: {} = {}", self.name, ty, value),
            (Some(ty), None) => write!(f, "{}: {}", self.name, ty),
            (None, Some(value)) => write!(f, "{} = {}", self.name, value),
            (None, None) => write!(f, "{}", self.name),
        }
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
