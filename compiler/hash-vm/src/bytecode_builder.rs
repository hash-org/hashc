//! Hash Compiler VM bytecode building module. This module
//! holds utilities and data structures to generate bytecode and store
//! it in the format that the VM expects. This module
//! might be used by a backend to convert from the Hash IR into
//! bytecode.
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
