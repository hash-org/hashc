//! Hash Compiler AST library file
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![feature(generic_associated_types)]
#![feature(iter_intersperse)]

extern crate strum;
#[macro_use]
extern crate strum_macros;

pub mod ast;
pub mod count;
pub mod error;
mod fs;
pub mod ident;
pub mod keyword;
pub mod literal;
pub mod location;
pub mod module;
pub mod operator;
pub mod parse;
pub mod resolve;
pub mod storage;
pub mod tests;
pub mod tree;
pub mod visitor;
pub mod visualise;
