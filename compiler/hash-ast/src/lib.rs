//! Hash Compiler AST library file

#![feature(box_into_inner, iter_intersperse, let_chains, lazy_cell)]

pub mod ast;
pub mod node_map;
pub mod origin;
pub mod tree;
pub mod visitor {
    pub use super::ast::{
        walk, walk_mut, walk_mut_self, AstVisitor, AstVisitorMut, AstVisitorMutSelf,
    };
}
