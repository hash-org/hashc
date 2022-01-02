//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::ident::Identifier;
use hashbrown::HashMap;

use crate::{
    bytecode::Instruction,
    error::RuntimeError,
    heap::{Heap, HeapValue},
};

// TODO: We shouldn't be using an identifier here, we need to use a symbol referencing some thing either that is located in the heap
// or the stack
struct FunctionCtx {
    symbols: HashMap<Identifier, HeapValue>,
}

struct Function {
    block: Vec<Instruction>,
    arity: u8,
    name: Vec<Identifier>,
    captured_ctx: Box<FunctionCtx>,
}

struct Stack {}
struct CallFrame {
    function: Box<Function>,
    ip: usize,
    base: usize,
}

struct Interpreter {
    stack: Box<Stack>,
    frames: Vec<CallFrame>,

    current_instruction: usize,
    instructions: Vec<Instruction>,

    heap: Heap,

    // TODO: symbol table: Strings, Integers, Floats, etc...
    constants: (),
}

impl Interpreter {
    fn run_next_instruction(&mut self) -> Result<(), RuntimeError> {
        let instruction = unsafe { self.instructions.get_unchecked(self.current_instruction) };

        match instruction {
            Instruction::Return {} => {}
            _ => panic!("Unimplemented instruction"),
        };

        Ok(())
    }

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        while self.current_instruction < self.instructions.len() {
            // Ok, now we need to run the current instruction, so we pass it into the run_next_instruction,
            // it's possible that the the next instruction will jump or invoke some kind of exit condition in
            // the VM, therefore we have to check after each invocation of the instruction if we can proceed
            self.run_next_instruction()?;

            // TODO: we probably need to refactor this out into a function as the 'done' state will become
            //       significantly more complicated...
            if self.current_instruction == self.instructions.len() {
                return Ok(());
            }

            self.current_instruction += 1;
        }

        Ok(())
    }
}
