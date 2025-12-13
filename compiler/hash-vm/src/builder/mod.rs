//! Hash Compiler VM bytecode building module.
//!
//! This module holds utilities and data structures to generate bytecode and
//! store it in the format that the VM expects.

mod func;
mod instruction;

use std::collections::HashMap;

use hash_abi::FnAbiId;

use crate::{
    builder::func::FunctionBuilder,
    bytecode::{Instruction, op::Operand},
};

#[derive(Debug)]
pub struct FunctionCtx {
    /// The ABI of the function, this is used to generate
    /// the correct instructions for the function, to read the
    /// arguments and return values correctly.
    pub abi: FnAbiId,

    /// The address of the function within the entire bytecode program.
    pub offset: usize,
}

#[derive(Debug, Default)]
pub struct BytecodeBuilder {
    /// The entire bytecode program, this contains all of the
    /// functions and their instructions.
    pub instructions: Vec<Instruction>,

    /// The function context store, this is used to store the function contexts.
    function_ctxs: HashMap<FnAbiId, FunctionCtx>,
}

impl BytecodeBuilder {
    pub fn new() -> Self {
        Self { instructions: Vec::new(), function_ctxs: HashMap::new() }
    }

    pub fn absorb(&mut self, func: &FunctionBuilder) -> usize {
        let FunctionBuilder { body, labels, .. } = func;
        let offset = self.instructions.len();

        // Reserve space for the function body instructions.
        self.instructions.reserve(body.len());

        // We need to resolve all of the labels within the function body, i.e. they
        // should now use the "global" offsets within the entire bytecode
        // program, rather than the relative offsets within the function body.
        for mut instruction in body.into_iter().copied() {
            match &mut instruction {
                Instruction::Jmp { location, .. }
                | Instruction::JmpPos { location, .. }
                | Instruction::JmpNeg { location, .. }
                | Instruction::JmpZero { location, .. } => {
                    if let Operand::Label(label) = *location {
                        // Resolve the label offset to the global instruction offset
                        let function_label = labels[label].get();
                        let global_offset = function_label + offset;
                        *location = Operand::Immediate(global_offset);
                    }
                }
                _ => {}
            }

            self.instructions.push(instruction);
        }

        offset
    }

    pub fn add_function(&mut self, fn_builder: FunctionBuilder) {
        // Absorb all of the function instructions into the bytecode builder.
        let start = self.absorb(&fn_builder);

        let FunctionBuilder { abi, .. } = fn_builder;
        let ctx = FunctionCtx { abi, offset: start };
        self.function_ctxs.insert(abi, ctx);
    }

    pub fn add_instruction(&mut self, instruction: Instruction) {
        self.instructions.push(instruction);
    }

    /// Append a block of instructions to the bytecode builder.
    ///
    /// This method accepts a `Vec<Instruction>` which can be conveniently
    /// created using the `inst!` macro.
    ///
    /// # Example
    ///
    /// ```
    /// use hash_vm::{builder::BytecodeBuilder, inst};
    ///
    /// let mut builder = BytecodeBuilder::new();
    /// builder.append(inst! {
    ///     write64 [0], # [42];
    ///     add64 [0], [1];
    /// });
    /// ```
    pub fn append(&mut self, instructions: Vec<Instruction>) {
        self.instructions.extend(instructions);
    }

    pub fn build(self) -> Vec<Instruction> {
        self.instructions
    }
}
