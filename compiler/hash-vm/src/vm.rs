//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::ident::Identifier;

use crate::{
    bytecode::{Instruction, Register, RegisterSet},
    error::RuntimeError,
    heap::Heap,
    stack::Stack,
};

struct Function {
    block: Vec<Instruction>,
    arity: u8,
    name: Vec<Identifier>,
}

struct CallFrame {
    function: Box<Function>,
    base: usize,
    offset: usize,
}

struct Interpreter {
    stack: Stack,
    frames: Vec<CallFrame>,

    instructions: Vec<Instruction>,

    /// We have 256 registers available to the interpreter at any time
    registers: RegisterSet,

    /// The VM Heap containing a bunch of objects
    heap: Heap,

    // TODO: symbol table: Strings, Integers, Floats, etc...
    constants: (),
}

impl Interpreter {
    fn run_next_instruction(&mut self) -> Result<(), RuntimeError> {
        let ip = self.get_instruction_pointer();
        let instruction = unsafe { self.instructions.get_unchecked(ip) };

        match instruction {
            Instruction::Return => {}
            Instruction::Add8 { l1, l2 } => todo!(),
            Instruction::Sub8 { l1, l2 } => todo!(),
            Instruction::Div8 { l1, l2 } => todo!(),
            Instruction::Mul8 { l1, l2 } => todo!(),
            Instruction::Mod8 { l1, l2 } => todo!(),
            Instruction::Add16 { l1, l2 } => todo!(),
            Instruction::Sub16 { l1, l2 } => todo!(),
            Instruction::Div16 { l1, l2 } => todo!(),
            Instruction::Mul16 { l1, l2 } => todo!(),
            Instruction::Mod16 { l1, l2 } => todo!(),
            Instruction::Add32 { l1, l2 } => todo!(),
            Instruction::Sub32 { l1, l2 } => todo!(),
            Instruction::Div32 { l1, l2 } => todo!(),
            Instruction::Mul32 { l1, l2 } => todo!(),
            Instruction::Mod32 { l1, l2 } => todo!(),
            Instruction::Add64 { l1, l2 } => todo!(),
            Instruction::Sub64 { l1, l2 } => todo!(),
            Instruction::Div64 { l1, l2 } => todo!(),
            Instruction::Mul64 { l1, l2 } => todo!(),
            Instruction::Mod64 { l1, l2 } => todo!(),
            Instruction::IDiv8 { l1, l2 } => todo!(),
            Instruction::IMul8 { l1, l2 } => todo!(),
            Instruction::IDiv16 { l1, l2 } => todo!(),
            Instruction::IMul16 { l1, l2 } => todo!(),
            Instruction::IDiv32 { l1, l2 } => todo!(),
            Instruction::IMul32 { l1, l2 } => todo!(),
            Instruction::IDiv64 { l1, l2 } => todo!(),
            Instruction::IMul64 { l1, l2 } => todo!(),
            Instruction::Xor { l1, l2 } => todo!(),
            Instruction::Or { l1, l2 } => todo!(),
            Instruction::And { l1, l2 } => todo!(),
            Instruction::Not { l1 } => todo!(),
            Instruction::PowF32 { l1, l2 } => todo!(),
            Instruction::PowF64 { l1, l2 } => todo!(),
            Instruction::Shl8 { l1, l2 } => todo!(),
            Instruction::Shr8 { l1, l2 } => todo!(),
            Instruction::Shl16 { l1, l2 } => todo!(),
            Instruction::Shr16 { l1, l2 } => todo!(),
            Instruction::Shl32 { l1, l2 } => todo!(),
            Instruction::Shr32 { l1, l2 } => todo!(),
            Instruction::Shl64 { l1, l2 } => todo!(),
            Instruction::Shr64 { l1, l2 } => todo!(),
            Instruction::Call { func } => todo!(),
            Instruction::Mov { src, dest } => todo!(),
            Instruction::Syscall { id } => todo!(),
            Instruction::Jmp { location } => todo!(),
            Instruction::JmpPos { l1, location } => todo!(),
            Instruction::JmpNeg { l1, location } => todo!(),
            Instruction::JmpZero { l1, location } => todo!(),
            Instruction::Cmp { l1, l2 } => todo!(),
            Instruction::Pop8 { l1 } => todo!(),
            Instruction::Pop16 { l1 } => todo!(),
            Instruction::Pop32 { l1 } => todo!(),
            Instruction::Pop64 { l1 } => todo!(),
            Instruction::Push8 { l1 } => todo!(),
            Instruction::Push16 { l1 } => todo!(),
            Instruction::Push32 { l1 } => todo!(),
            Instruction::Push64 { l1 } => todo!(),
            // _ => panic!("Unimplemented instruction"),
        };

        Ok(())
    }

    /// Gets the current instruction pointer of the VM.
    pub fn get_instruction_pointer(&self) -> usize {
        self.registers
            .get_register64(Register::INSTRUCTION_POINTER)
            .try_into()
            .unwrap()
    }

    /// Sets the current instruction pointer of the VM.
    pub fn set_instruction_pointer(&mut self, value: usize) {
        self.registers
            .set_register64(Register::INSTRUCTION_POINTER, value.try_into().unwrap());
    }

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        let ip = self.get_instruction_pointer();

        while ip < self.instructions.len() {
            // Ok, now we need to run the current instruction, so we pass it into the run_next_instruction,
            // it's possible that the the next instruction will jump or invoke some kind of exit condition in
            // the VM, therefore we have to check after each invocation of the instruction if we can proceed
            self.run_next_instruction()?;

            // TODO: we probably need to refactor this out into a function as the 'done' state will become
            //       significantly more complicated...
            if ip == self.instructions.len() {
                return Ok(());
            }

            self.set_instruction_pointer(ip + 1);
        }

        Ok(())
    }
}
