//! Hash Compiler Frontend library file
//
// All rights reserved 2021 (c) The Hash Language authors

extern crate pest;

#[macro_use]
extern crate lazy_static;

pub mod ast;
pub mod emit;
pub mod error;
pub mod parse;

mod grammar;
mod location;
mod modules;
mod precedence;
