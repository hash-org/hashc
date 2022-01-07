//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code, unused)]
#![feature(unchecked_math)]

mod bytecode;
mod bytecode_builder;
pub mod error;
mod heap;
mod stack;
pub mod vm;
