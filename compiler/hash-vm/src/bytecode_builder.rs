//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_alloc::{collections::row::Row, row, Wall};

use crate::bytecode::Instruction;

// @@TODO: here we want to implement some kind of trait that's defined in HIR so that essentially we can build
//       the bytecode from the produces HIR.

pub struct BytecodeBuilder<'w, 'c> {
    instructions: Row<'c, Instruction>,

    /// The castle allocator for the current [BytecodeBuilder].
    wall: &'w Wall<'c>,
}

impl<'w, 'c> BytecodeBuilder<'w, 'c> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        BytecodeBuilder {
            instructions: row![wall;],
            wall,
        }
    }

    pub fn add_instruction(&mut self, instruction: Instruction) -> &mut Self {
        self.instructions.push(instruction, self.wall);
        self
    }
}
