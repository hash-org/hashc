//! Definitions related to block terms and declarations inside them.
use core::fmt;

use hash_storage::{
    get,
    store::{statics::StoreId, TrivialSequenceStoreKey},
};
use textwrap::indent;

use crate::{
    stack::StackId,
    stores::tir_stores,
    tir::{Pat, PatId, Term, TermId, TyId},
    tir_node_sequence_store_direct,
};
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
    pub value: TermId,
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

/// A block term.
///
/// Creates a new scope on the stack.
#[derive(Debug, Clone, Copy)]
pub struct BlockTerm {
    pub stack_id: StackId, // The associated stack ID for this block.
    pub statements: BlockStatementsId,
    pub expr: TermId,
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = match *self.bind_pat.value() {
            Pat::Binding(binding_pat) => {
                match *self.value.value() {
                    // If a function is being declared, print the body, otherwise just
                    // its name.
                    Term::Fn(fn_def_id) if fn_def_id.map(|def| def.name == binding_pat.name) => {
                        fn_def_id.to_string()
                    }
                    _ => self.value.to_string(),
                }
            }
            _ => self.value.to_string(),
        };

        write!(f, "{}: {} = {}", self.bind_pat, self.ty, value,)
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
