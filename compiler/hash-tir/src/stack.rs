//! Definitions related to stack scopes.

use core::fmt;

use hash_storage::{get, store::statics::StoreId};
use textwrap::indent;

use crate::{
    context::ContextMember,
    stores::tir_stores,
    tir::{ModDefId, Node, NodeOrigin},
    tir_node_single_store,
};

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
