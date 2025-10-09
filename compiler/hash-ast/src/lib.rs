//! Hash Compiler AST library file

#![feature(box_into_inner, iter_intersperse)]

pub mod ast;
pub mod node_map;
pub mod origin;

pub mod visitor {
    pub use super::ast::{
        AstVisitor, AstVisitorMut, AstVisitorMutSelf, walk, walk_mut, walk_mut_self,
    };
}
