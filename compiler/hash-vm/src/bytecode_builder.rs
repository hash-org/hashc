//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::bytecode::Instruction;

// @@TODO: here we want to implement some kind of trait that's defined in HIR so that essentially we can build
//       the bytecode from the produces HIR.

#[derive(Debug, Default)]
pub struct BytecodeBuilder {
    instructions: Vec<Instruction>,
}

impl BytecodeBuilder {
    pub fn add_instruction(&mut self, instruction: Instruction) -> &mut Self {
        self.instructions.push(instruction);
        self
    }
}

impl From<BytecodeBuilder> for Vec<Instruction> {
    fn from(builder: BytecodeBuilder) -> Self {
        builder.instructions
    }
}
