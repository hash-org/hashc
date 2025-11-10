//! Hash Compiler VM bytecode building module.
//!
//! This module holds utilities and data structures to generate bytecode and
//! store it in the format that the VM expects.
use crate::bytecode::Instruction;

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
