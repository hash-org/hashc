//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#[derive(Debug)]
pub struct Register {}

#[derive(Debug)]
pub enum Instruction {
    Return {},
    Add {
        l1: Register,
        l2: Register,
        result: Register,
    },
}
