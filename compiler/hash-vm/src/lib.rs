//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![feature(unchecked_math)]

mod heap;
mod stack;

pub mod bytecode;
pub mod register;

pub mod bytecode_builder;
pub mod error;
pub mod vm;
