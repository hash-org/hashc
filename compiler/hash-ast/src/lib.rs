//! Hash Compiler AST library file
//!
//! All rights reserved 2022 (c) The Hash Language authors
#![feature(generic_associated_types, box_into_inner, iter_intersperse)]

use hash_alloc::Castle;
use lazy_static::lazy_static;

lazy_static! {
    /// AST static allocator
    pub static ref STATIC_CASTLE: Castle = Castle::new();
}

pub mod ast;
pub mod literal;
pub mod operator;
pub mod tree;
pub mod visitor;
