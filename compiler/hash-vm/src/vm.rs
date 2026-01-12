//! Hash Compiler virtual machine implementation and bytecode runner.

use std::cell::Cell;

use crate::{
    bytecode::{
        Instruction, Operand,
        register::{Register, RegisterSet},
    },
    error::RuntimeError,
    memory::{HasMemoryAccess, Memory},
};

/// Interpreter flags represent generated context from the current
/// execution. This flags store information about the last executed
/// instruction (if relevant).
#[derive(Debug, Default)]
pub struct InterpreterFlags {
    /// If the recent arithmetic operation resulted in an 'overflow'
    pub overflow: Cell<bool>,

    /// Result from performing a comparison
    pub comparison: Cell<i64>,
}

/// The [Interpreter] is a structure representing the current execution context
/// of the program. It contains the program stack, heap, instruction vector,
/// registers, etc.
#[derive(Debug)]
pub struct Interpreter {
    /// The memory space of the VM.
    memory: Memory,

    /// A vector of [Instruction]s representing the program that it will run.
    instructions: Vec<Instruction>,

    /// The [Register]s available to the interpreter at any time.
    registers: RegisterSet,

    /// Interpreter flags represent the result of some operation that has
    /// occurred
    flags: InterpreterFlags,
}

impl Interpreter {
    #[must_use]
    pub fn new(memory: Memory) -> Self {
        Self {
            memory,
            instructions: Vec::new(),
            registers: RegisterSet::default(),
            flags: InterpreterFlags::default(),
        }
    }

    /// Get a reference to the current program space.
    pub fn program(&self) -> &[Instruction] {
        &self.instructions
    }

    fn run_next_instruction(&mut self) -> Result<(), RuntimeError> {
        let ip = self.get_instruction_pointer();
        let sp = self.get_stack_pointer();
        let instruction = self.instructions.get(ip).unwrap();

        match *instruction {
            Instruction::Add8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                // Check whether an overflow occurs when adding, if an overflow does occur, we
                // set the `overflow` interpreter flag, otherwise set it to false
                match r1.checked_add(r2) {
                    Some(result) => {
                        self.registers.set_register8(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register8(l1, r1.wrapping_add(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Sub8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                match r1.checked_sub(r2) {
                    Some(result) => {
                        self.registers.set_register8(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register8(l1, r1.wrapping_sub(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Div8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register8(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register8(l1, r1.wrapping_div(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mul8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register8(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register8(l1, r1.wrapping_mul(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mod8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                match r1.checked_rem(r2) {
                    Some(result) => {
                        self.registers.set_register8(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register8(l1, r1.wrapping_rem(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Add16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                match r1.checked_add(r2) {
                    Some(result) => {
                        self.registers.set_register16(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register16(l1, r1.wrapping_add(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Sub16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                match r1.checked_sub(r2) {
                    Some(result) => {
                        self.registers.set_register16(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register16(l1, r1.wrapping_sub(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Div16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register16(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register16(l1, r1.wrapping_div(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mul16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register16(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register16(l1, r1.wrapping_mul(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mod16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                match r1.checked_rem(r2) {
                    Some(result) => {
                        self.registers.set_register16(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register16(l1, r1.wrapping_rem(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Add32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                match r1.checked_add(r2) {
                    Some(result) => {
                        self.registers.set_register32(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register32(l1, r1.wrapping_add(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Sub32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                match r1.checked_sub(r2) {
                    Some(result) => {
                        self.registers.set_register32(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register32(l1, r1.wrapping_sub(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Div32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register32(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register32(l1, r1.wrapping_div(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mul32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register32(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register32(l1, r1.wrapping_mul(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mod32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                match r1.checked_rem(r2) {
                    Some(result) => {
                        self.registers.set_register32(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register32(l1, r1.wrapping_rem(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Add64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                match r1.checked_add(r2) {
                    Some(result) => {
                        self.registers.set_register64(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register64(l1, r1.wrapping_add(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Sub64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                match r1.checked_sub(r2) {
                    Some(result) => {
                        self.registers.set_register64(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register64(l1, r1.wrapping_sub(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Div64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register64(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register64(l1, r1.wrapping_div(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mul64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register64(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register64(l1, r1.wrapping_mul(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::Mod64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                match r1.checked_rem(r2) {
                    Some(result) => {
                        self.registers.set_register64(l1, result);
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register64(l1, r1.wrapping_rem(r2));
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IDiv8 { l1, l2 } => {
                let r1 = i8::from_be_bytes(*self.registers.get_register_b(l1));
                let r2 = i8::from_be_bytes(*self.registers.get_register_b(l2));

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register_b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_b(l1, &r1.wrapping_div(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IMul8 { l1, l2 } => {
                let r1 = i8::from_be_bytes(*self.registers.get_register_b(l1));
                let r2 = i8::from_be_bytes(*self.registers.get_register_b(l2));

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register_b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_b(l1, &r1.wrapping_mul(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IDiv16 { l1, l2 } => {
                let r1 = i16::from_be_bytes(*self.registers.get_register_2b(l1));
                let r2 = i16::from_be_bytes(*self.registers.get_register_2b(l2));

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register_2b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_2b(l1, &r1.wrapping_mul(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IMul16 { l1, l2 } => {
                let r1 = i16::from_be_bytes(*self.registers.get_register_2b(l1));
                let r2 = i16::from_be_bytes(*self.registers.get_register_2b(l2));

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register_2b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_2b(l1, &r1.wrapping_mul(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IDiv32 { l1, l2 } => {
                let r1 = i32::from_be_bytes(*self.registers.get_register_4b(l1));
                let r2 = i32::from_be_bytes(*self.registers.get_register_4b(l2));

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register_4b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_4b(l1, &r1.wrapping_div(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IMul32 { l1, l2 } => {
                let r1 = i32::from_be_bytes(*self.registers.get_register_4b(l1));
                let r2 = i32::from_be_bytes(*self.registers.get_register_4b(l2));

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register_4b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_4b(l1, &r1.wrapping_mul(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IDiv64 { l1, l2 } => {
                let r1 = i64::from_be_bytes(*self.registers.get_register_8b(l1));
                let r2 = i64::from_be_bytes(*self.registers.get_register_8b(l2));

                match r1.checked_div(r2) {
                    Some(result) => {
                        self.registers.set_register_8b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_8b(l1, &r1.wrapping_div(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::IMul64 { l1, l2 } => {
                let r1 = i64::from_be_bytes(*self.registers.get_register_8b(l1));
                let r2 = i64::from_be_bytes(*self.registers.get_register_8b(l2));

                match r1.checked_mul(r2) {
                    Some(result) => {
                        self.registers.set_register_8b(l1, &result.to_be_bytes());
                        self.flags.overflow.set(false);
                    }
                    None => {
                        self.registers.set_register_8b(l1, &r1.wrapping_mul(r2).to_be_bytes());
                        self.flags.overflow.set(true);
                    }
                }
            }
            Instruction::AddF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_f32(l1, r1 + r2);
            }
            Instruction::SubF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_f32(l1, r1 - r2);
            }
            Instruction::DivF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_f32(l1, r1 / r2);
            }
            Instruction::MulF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_f32(l1, r1 * r2);
            }
            Instruction::ModF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_f32(l1, r1 % r2);
            }
            Instruction::AddF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_f64(l1, r1 + r2);
            }
            Instruction::SubF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_f64(l1, r1 - r2);
            }
            Instruction::DivF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_f64(l1, r1 / r2);
            }
            Instruction::MulF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_f64(l1, r1 * r2);
            }
            Instruction::ModF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_f64(l1, r1 % r2);
            }
            Instruction::Xor8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                self.registers.set_register8(l1, r1 ^ r2);
            }
            Instruction::Xor16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                self.registers.set_register16(l1, r1 ^ r2);
            }
            Instruction::Xor32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                self.registers.set_register32(l1, r1 ^ r2);
            }
            Instruction::Xor64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                self.registers.set_register64(l1, r1 ^ r2);
            }
            Instruction::Or8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                self.registers.set_register8(l1, r1 | r2);
            }
            Instruction::Or16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                self.registers.set_register16(l1, r1 | r2);
            }
            Instruction::Or32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                self.registers.set_register32(l1, r1 | r2);
            }
            Instruction::Or64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                self.registers.set_register64(l1, r1 | r2);
            }
            Instruction::And8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                self.registers.set_register8(l1, r1 & r2);
            }
            Instruction::And16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                self.registers.set_register16(l1, r1 & r2);
            }
            Instruction::And32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                self.registers.set_register32(l1, r1 & r2);
            }
            Instruction::And64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                self.registers.set_register64(l1, r1 & r2);
            }
            Instruction::Not8 { l1 } => {
                let r1 = self.registers.get_register8(l1);

                self.registers.set_register8(l1, !r1);
            }
            Instruction::Not16 { l1 } => {
                let r1 = self.registers.get_register16(l1);

                self.registers.set_register16(l1, !r1);
            }
            Instruction::Not32 { l1 } => {
                let r1 = self.registers.get_register32(l1);

                self.registers.set_register32(l1, !r1);
            }
            Instruction::Not64 { l1 } => {
                let r1 = self.registers.get_register64(l1);

                self.registers.set_register64(l1, !r1);
            }
            Instruction::PowF32 { l1, l2 } => {
                let r1 = self.registers.get_register_f32(l1);
                let r2 = self.registers.get_register_f32(l2);

                self.registers.set_register_4b(l1, &r1.powf(r2).to_be_bytes());
            }
            Instruction::PowF64 { l1, l2 } => {
                let r1 = self.registers.get_register_f64(l1);
                let r2 = self.registers.get_register_f64(l2);

                self.registers.set_register_8b(l1, &r1.powf(r2).to_be_bytes());
            }
            Instruction::Shl8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                self.registers.set_register_b(l1, &(r1 << r2).to_be_bytes());
            }
            Instruction::Shr8 { l1, l2 } => {
                let r1 = self.registers.get_register8(l1);
                let r2 = self.registers.get_register8(l2);

                self.registers.set_register_b(l1, &(r1 >> r2).to_be_bytes());
            }
            Instruction::Shl16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                self.registers.set_register16(l1, r1 << r2);
            }
            Instruction::Shr16 { l1, l2 } => {
                let r1 = self.registers.get_register16(l1);
                let r2 = self.registers.get_register16(l2);

                self.registers.set_register16(l1, r1 >> r2);
            }
            Instruction::Shl32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                self.registers.set_register32(l1, r1 << r2);
            }
            Instruction::Shr32 { l1, l2 } => {
                let r1 = self.registers.get_register32(l1);
                let r2 = self.registers.get_register32(l2);

                self.registers.set_register32(l1, r1 >> r2);
            }
            Instruction::Shl64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                self.registers.set_register64(l1, r1 << r2);
            }
            Instruction::Shr64 { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                self.registers.set_register64(l1, r1 >> r2);
            }
            Instruction::Mov { src, dest } => {
                let value = self.registers.get_register64(src);
                self.registers.set_register64(dest, value);
            }
            Instruction::Jmp { location } => {
                // Arbitrarily jump to the specified location in the register
                let value = location.as_literal_usize(&self.registers);
                self.set_instruction_pointer(value);
            }
            Instruction::JmpPos { l1, location } => {
                let r1 = i64::from_be_bytes(*self.registers.get_register_8b(l1));

                // Arbitrarily jump to the specified location in the register if the comparison
                // value is less than zero or in other words, negative...
                if r1 > 0 {
                    let value = location.as_literal_usize(&self.registers);
                    self.set_instruction_pointer(value);
                }
            }
            Instruction::JmpNeg { l1, location } => {
                let r1 = i64::from_be_bytes(*self.registers.get_register_8b(l1));

                // Arbitrarily jump to the specified location in the register if the comparison
                // value is less than zero or in other words, negative...
                if r1 < 0 {
                    let value = location.as_literal_usize(&self.registers);
                    self.set_instruction_pointer(value);
                }
            }
            Instruction::JmpZero { l1, location } => {
                let r1 = i64::from_be_bytes(*self.registers.get_register_8b(l1));

                // Arbitrarily jump to the specified location in the register if the comparison
                // value is less than zero or in other words, negative...
                if r1 == 0 {
                    let value = location.as_literal_usize(&self.registers);
                    self.set_instruction_pointer(value);
                }
            }
            Instruction::Cmp { l1, l2 } => {
                let r1 = self.registers.get_register64(l1);
                let r2 = self.registers.get_register64(l2);

                let value = if r1 >= r2 {
                    (r1 - r2).to_be_bytes()
                } else {
                    (-((r2 - r1) as i64)).to_be_bytes()
                };

                self.registers.set_register_8b(l1, &value);
            }
            Instruction::Pop8 { l1 } => {
                // Pop the top byte on top of the stack and put it into the register
                let value = self.memory.read8(sp)?;
                self.registers.set_register_b(l1, value);
                self.set_stack_pointer(sp - 1);
            }
            Instruction::Pop16 { l1 } => {
                // Pop the top two bytes on top of the stack and put it into the register
                let value = self.memory.read16(sp)?;
                self.registers.set_register_2b(l1, value);
                self.set_stack_pointer(sp - 2);
            }
            Instruction::Pop32 { l1 } => {
                // Pop the top four bytes on top of the stack and put it into the register
                let value = self.memory.read32(sp)?;
                self.registers.set_register_4b(l1, value);
                self.set_stack_pointer(sp - 4);
            }
            Instruction::Pop64 { l1 } => {
                // Pop the top four bytes on top of the stack and put it into the register
                let value = self.memory.read64(sp)?;
                self.registers.set_register_8b(l1, value);
                self.set_stack_pointer(sp - 8);
            }
            Instruction::Push8 { l1 } => {
                let value = self.registers.get_register_b(l1);
                self.memory.write8(sp, value)?;
                self.set_stack_pointer(sp + 1);
            }
            Instruction::Push16 { l1 } => {
                let value = self.registers.get_register_2b(l1);
                self.memory.write16(sp, value)?;
                self.set_stack_pointer(sp + 2);
            }
            Instruction::Push32 { l1 } => {
                let value = self.registers.get_register_4b(l1);
                self.memory.write32(sp, value)?;
                self.set_stack_pointer(sp + 4);
            }
            Instruction::Push64 { l1 } => {
                let value = self.registers.get_register_8b(l1);
                self.memory.write64(sp, value)?;
                self.set_stack_pointer(sp + 8);
            }
            Instruction::Call { func } => {
                // Save the ip onto the stack
                self.memory.write64(
                    sp,
                    &self.registers.get_register64(Register::INSTRUCTION_POINTER).to_be_bytes(),
                )?;
                self.set_stack_pointer(self.get_stack_pointer() + 8);

                // Save the bp onto the stack
                self.memory.write64(
                    sp,
                    &self.registers.get_register64(Register::BASE_POINTER).to_be_bytes(),
                )?;
                self.set_stack_pointer(sp + 8);

                // Set the new bp as the stack pointer
                self.registers.set_register64(
                    Register::BASE_POINTER,
                    self.registers.get_register64(Register::STACK_POINTER),
                );

                // Jump to the function
                self.registers.set_register64(
                    Register::INSTRUCTION_POINTER,
                    self.registers.get_register64(func.as_register()),
                );
            }
            Instruction::Return => {
                // Set the stack pointer back to the base pointer
                self.registers.set_register64(
                    Register::STACK_POINTER,
                    self.registers.get_register64(Register::BASE_POINTER),
                );

                // Get the BP from stack and set it
                self.registers.set_register64(
                    Register::BASE_POINTER,
                    u64::from_be_bytes(*self.memory.read64(sp)?),
                );
                self.set_stack_pointer(sp - 8);

                // Get the IP from stack and set it
                self.registers.set_register64(
                    Register::INSTRUCTION_POINTER,
                    u64::from_be_bytes(*self.memory.read64(sp)?),
                );
                self.set_stack_pointer(sp - 16); // 8 for BP + 8 for IP
            }
            Instruction::Write8 { op, value } => {
                match op {
                    Operand::Register(reg) => {
                        self.registers.set_register8(reg, value);
                    }
                    Operand::Immediate(addr) => {
                        // write to the memory address in the stack.
                        self.memory.write8(addr, &value.to_be_bytes())?;
                    }
                    _ => unreachable!(),
                }
            }
            Instruction::Write16 { op, value } => {
                match op {
                    Operand::Register(reg) => {
                        self.registers.set_register16(reg, value);
                    }
                    Operand::Immediate(addr) => {
                        // write to the memory address in the stack.
                        self.memory.write16(addr, &value.to_be_bytes())?;
                    }
                    _ => unreachable!(),
                }
            }
            Instruction::Write32 { op, value } => {
                match op {
                    Operand::Register(reg) => {
                        self.registers.set_register32(reg, value);
                    }
                    Operand::Immediate(addr) => {
                        // write to the memory address in the stack.
                        self.memory.write32(addr, &value.to_be_bytes())?;
                    }
                    _ => unreachable!(),
                }
            }
            Instruction::Write64 { op, value } => {
                match op {
                    Operand::Register(reg) => {
                        self.registers.set_register64(reg, value);
                    }
                    Operand::Immediate(addr) => {
                        // write to the memory address in the stack.
                        self.memory.write64(addr, &value.to_be_bytes())?;
                    }
                    _ => unreachable!(),
                }
            }
            Instruction::Syscall { .. } => todo!(),
        };

        Ok(())
    }

    /// Get the current stack pointer of the VM.
    pub fn get_stack_pointer(&self) -> usize {
        self.registers.get_register64(Register::STACK_POINTER).try_into().unwrap()
    }

    /// Sets the current stack pointer of the VM.
    pub fn set_stack_pointer(&mut self, value: usize) {
        self.registers.set_register64(Register::STACK_POINTER, value.try_into().unwrap());
    }

    /// Gets the current instruction pointer of the VM.
    pub fn get_instruction_pointer(&self) -> usize {
        self.registers.get_register64(Register::INSTRUCTION_POINTER).try_into().unwrap()
    }

    /// Sets the current instruction pointer of the VM.
    pub fn set_instruction_pointer(&mut self, value: usize) {
        self.registers.set_register64(Register::INSTRUCTION_POINTER, value.try_into().unwrap());
    }

    pub fn set_program(&mut self, program: Vec<Instruction>) {
        self.instructions = program;
    }

    pub fn registers(&self) -> &RegisterSet {
        &self.registers
    }

    pub fn registers_mut(&mut self) -> &mut RegisterSet {
        &mut self.registers
    }

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        let mut ip = self.get_instruction_pointer();

        while ip < self.instructions.len() {
            // Ok, now we need to run the current instruction, so we pass it into the
            // run_next_instruction, it's possible that the the next instruction
            // will jump or invoke some kind of exit condition in
            // the VM, therefore we have to check after each invocation of the instruction
            // if we can proceed
            self.run_next_instruction()?;

            // TODO: we probably need to refactor this out into a function as the 'done'
            // state will become       significantly more complicated...
            if ip == self.instructions.len() - 1 {
                return Ok(());
            }

            ip += 1;
            self.set_instruction_pointer(ip);
        }

        Ok(())
    }
}
