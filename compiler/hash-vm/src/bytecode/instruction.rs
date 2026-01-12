use std::fmt;

use super::{op::Operand, register::Register};

/// The VM instruction set.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Instruction {
    /// Pop 8bit cell off the stack
    Pop8 {
        l1: Register,
    },
    /// Pop 16bit cell off the stack
    Pop16 {
        l1: Register,
    },
    /// Pop 32bit cell off the stack
    Pop32 {
        l1: Register,
    },
    /// Pop 64bit cell off the stack
    Pop64 {
        l1: Register,
    },
    /// Push 8bit cell onto stack
    Push8 {
        l1: Register,
    },
    /// Push 16bit cell onto stack
    Push16 {
        l1: Register,
    },
    /// Push 32bit cell onto stack
    Push32 {
        l1: Register,
    },
    /// Push 64bit cell onto stack
    Push64 {
        l1: Register,
    },
    /// Unsigned integer 8bit Addition
    Add8 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 16bit Addition
    Add16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Addition
    Add32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Addition
    Add64 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 8bit Subtraction
    Sub8 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 16bit Subtraction
    Sub16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Subtraction
    Sub32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Subtraction
    Sub64 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 8bit Division
    Div8 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 16bit Division
    Div16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Division
    Div32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Division
    Div64 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 8bit Multiplication
    Mul8 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 16bit Multiplication
    Mul16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Multiplication
    Mul32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Multiplication
    Mul64 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 8bit Modulo
    Mod8 {
        l1: Register,
        l2: Register,
    },
    /// Unsigned integer 16bit Modulo
    Mod16 {
        l1: Register,
        l2: Register,
    },

    /// Signed integer 32bit Modulo
    Mod32 {
        l1: Register,
        l2: Register,
    },

    /// Signed integer 64bit Modulo
    Mod64 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 8bit Division
    IDiv8 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 16bit Division
    IDiv16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Division
    IDiv32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Division
    IDiv64 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 8bit Multiplication
    IMul8 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 16bit Multiplication
    IMul16 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 32bit Multiplication
    IMul32 {
        l1: Register,
        l2: Register,
    },
    /// Signed integer 64bit Multiplication
    IMul64 {
        l1: Register,
        l2: Register,
    },
    /// Float 32bit Addition
    AddF32 {
        l1: Register,
        l2: Register,
    },
    /// Float 64bit Addition
    AddF64 {
        l1: Register,
        l2: Register,
    },
    /// Float 32bit Subtraction
    SubF32 {
        l1: Register,
        l2: Register,
    },
    /// Float 64bit Subtraction
    SubF64 {
        l1: Register,
        l2: Register,
    },
    /// Float 32bit Division
    DivF32 {
        l1: Register,
        l2: Register,
    },
    /// Float 64bit Division
    DivF64 {
        l1: Register,
        l2: Register,
    },
    /// Float 32bit Multiplication
    MulF32 {
        l1: Register,
        l2: Register,
    },
    /// Float 64bit Multiplication
    MulF64 {
        l1: Register,
        l2: Register,
    },
    /// Float 32bit Modulo
    ModF32 {
        l1: Register,
        l2: Register,
    },
    /// Float 64bit Modulo
    ModF64 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 8bit Exclusive OR
    Xor8 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 16bit Exclusive OR
    Xor16 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 32bit Exclusive OR
    Xor32 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 64bit Exclusive OR
    Xor64 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 8bit OR
    Or8 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 16bit OR
    Or16 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 32bit OR
    Or32 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 64bit OR
    Or64 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 8bit AND
    And8 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 16bit AND
    And16 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 32bit AND
    And32 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 64bit AND
    And64 {
        l1: Register,
        l2: Register,
    },
    // Bitwise 8bit NOT
    Not8 {
        l1: Register,
    },
    // Bitwise 16bit NOT
    Not16 {
        l1: Register,
    },
    // Bitwise 32bit NOT
    Not32 {
        l1: Register,
    },
    // Bitwise 64bit NOT
    Not64 {
        l1: Register,
    },
    /// 32bit exponentiation with floating point numbers
    PowF32 {
        l1: Register,
        l2: Register,
    },
    /// 64bit exponentiation with floating point numbers
    PowF64 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 8bit left-shift
    Shl8 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 16bit left-shift
    Shl16 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 32bit left-shift
    Shl32 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 64bit left-shift
    Shl64 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 8bit right-shift
    Shr8 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 16bit right-shift
    Shr16 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 32bit right-shift
    Shr32 {
        l1: Register,
        l2: Register,
    },
    /// Bitwise 64bit right-shift
    Shr64 {
        l1: Register,
        l2: Register,
    },
    /// Write an 8bit literal value to a memory address.
    Write8 {
        op: Operand,
        value: u8,
    },
    /// Write a 16bit literal value to a memory address.
    Write16 {
        op: Operand,
        value: u16,
    },
    /// Write a 32bit literal value to a memory address.
    Write32 {
        op: Operand,
        value: u32,
    },
    /// Write a 64bit literal value to a memory address.
    Write64 {
        op: Operand,
        value: u64,
    },
    /// Call a function at a given address
    Call {
        func: Operand,
    },
    /// Copy a value from source register to destination register.
    Mov {
        src: Register,
        dest: Register,
    },
    /// Invoke a system call with a particular ID
    Syscall {
        id: Register,
    },
    /// Return from the current function call
    Return,
    /// Unconditional jump
    Jmp {
        location: Operand,
    },
    /// Jump if the comparison value yields a '> zero', or in other words the
    /// right is greater than left
    JmpPos {
        l1: Register,
        location: Operand,
    },
    /// Jump if the comparison value yields a '< zero', or in other words the
    /// left is greater than right
    JmpNeg {
        l1: Register,
        location: Operand,
    },
    /// Jump if the comparison yields a 'zero', or in other words the left and
    /// right are equal
    JmpZero {
        l1: Register,
        location: Operand,
    },
    /// Compare both values and store the result in `l1`. This will return
    /// either a one, zero or negative one.
    Cmp {
        l1: Register,
        l2: Register,
    },
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Pop8 { l1 } => write!(f, "pop8 {}", l1),
            Instruction::Pop16 { l1 } => write!(f, "pop16 {}", l1),
            Instruction::Pop32 { l1 } => write!(f, "pop32 {}", l1),
            Instruction::Pop64 { l1 } => write!(f, "pop64 {}", l1),
            Instruction::Push8 { l1 } => write!(f, "push8 {}", l1),
            Instruction::Push16 { l1 } => write!(f, "push16 {}", l1),
            Instruction::Push32 { l1 } => write!(f, "push32 {}", l1),
            Instruction::Push64 { l1 } => write!(f, "push64 {}", l1),
            Instruction::Add8 { l1, l2 } => write!(f, "add8 {}, {}", l1, l2),
            Instruction::Add16 { l1, l2 } => write!(f, "add16 {}, {}", l1, l2),
            Instruction::Add32 { l1, l2 } => write!(f, "add32 {}, {}", l1, l2),
            Instruction::Add64 { l1, l2 } => write!(f, "add64 {}, {}", l1, l2),
            Instruction::Sub8 { l1, l2 } => write!(f, "sub8 {}, {}", l1, l2),
            Instruction::Sub16 { l1, l2 } => write!(f, "sub16 {}, {}", l1, l2),
            Instruction::Sub32 { l1, l2 } => write!(f, "sub32 {}, {}", l1, l2),
            Instruction::Sub64 { l1, l2 } => write!(f, "sub64 {}, {}", l1, l2),
            Instruction::Div8 { l1, l2 } => write!(f, "div8 {}, {}", l1, l2),
            Instruction::Div16 { l1, l2 } => write!(f, "div16 {}, {}", l1, l2),
            Instruction::Div32 { l1, l2 } => write!(f, "div32 {}, {}", l1, l2),
            Instruction::Div64 { l1, l2 } => write!(f, "div64 {}, {}", l1, l2),
            Instruction::Mul8 { l1, l2 } => write!(f, "mul8 {}, {}", l1, l2),
            Instruction::Mul16 { l1, l2 } => write!(f, "mul16 {}, {}", l1, l2),
            Instruction::Mul32 { l1, l2 } => write!(f, "mul32 {}, {}", l1, l2),
            Instruction::Mul64 { l1, l2 } => write!(f, "mul64 {}, {}", l1, l2),
            Instruction::Mod8 { l1, l2 } => write!(f, "mod8 {}, {}", l1, l2),
            Instruction::Mod16 { l1, l2 } => write!(f, "mod16 {}, {}", l1, l2),
            Instruction::Mod32 { l1, l2 } => write!(f, "mod32 {}, {}", l1, l2),
            Instruction::Mod64 { l1, l2 } => write!(f, "mod64 {}, {}", l1, l2),
            Instruction::IDiv8 { l1, l2 } => write!(f, "idiv8 {}, {}", l1, l2),
            Instruction::IDiv16 { l1, l2 } => write!(f, "idiv16 {}, {}", l1, l2),
            Instruction::IDiv32 { l1, l2 } => write!(f, "idiv32 {}, {}", l1, l2),
            Instruction::IDiv64 { l1, l2 } => write!(f, "idiv64 {}, {}", l1, l2),
            Instruction::IMul8 { l1, l2 } => write!(f, "imul8 {}, {}", l1, l2),
            Instruction::IMul16 { l1, l2 } => write!(f, "imul16 {}, {}", l1, l2),
            Instruction::IMul32 { l1, l2 } => write!(f, "imul32 {}, {}", l1, l2),
            Instruction::IMul64 { l1, l2 } => write!(f, "imul64 {}, {}", l1, l2),
            Instruction::AddF32 { l1, l2 } => write!(f, "addf32 {}, {}", l1, l2),
            Instruction::AddF64 { l1, l2 } => write!(f, "addf64 {}, {}", l1, l2),
            Instruction::SubF32 { l1, l2 } => write!(f, "subf32 {}, {}", l1, l2),
            Instruction::SubF64 { l1, l2 } => write!(f, "subf64 {}, {}", l1, l2),
            Instruction::DivF32 { l1, l2 } => write!(f, "divf32 {}, {}", l1, l2),
            Instruction::DivF64 { l1, l2 } => write!(f, "divf64 {}, {}", l1, l2),
            Instruction::MulF32 { l1, l2 } => write!(f, "mulf32 {}, {}", l1, l2),
            Instruction::MulF64 { l1, l2 } => write!(f, "mulf64 {}, {}", l1, l2),
            Instruction::ModF32 { l1, l2 } => write!(f, "modf32 {}, {}", l1, l2),
            Instruction::ModF64 { l1, l2 } => write!(f, "modf64 {}, {}", l1, l2),
            Instruction::Xor8 { l1, l2 } => write!(f, "xor8 {}, {}", l1, l2),
            Instruction::Xor16 { l1, l2 } => write!(f, "xor16 {}, {}", l1, l2),
            Instruction::Xor32 { l1, l2 } => write!(f, "xor32 {}, {}", l1, l2),
            Instruction::Xor64 { l1, l2 } => write!(f, "xor64 {}, {}", l1, l2),
            Instruction::Or8 { l1, l2 } => write!(f, "or8 {}, {}", l1, l2),
            Instruction::Or16 { l1, l2 } => write!(f, "or16 {}, {}", l1, l2),
            Instruction::Or32 { l1, l2 } => write!(f, "or32 {}, {}", l1, l2),
            Instruction::Or64 { l1, l2 } => write!(f, "or64 {}, {}", l1, l2),
            Instruction::And8 { l1, l2 } => write!(f, "and8 {}, {}", l1, l2),
            Instruction::And16 { l1, l2 } => write!(f, "and16 {}, {}", l1, l2),
            Instruction::And32 { l1, l2 } => write!(f, "and32 {}, {}", l1, l2),
            Instruction::And64 { l1, l2 } => write!(f, "and64 {}, {}", l1, l2),
            Instruction::Not8 { l1 } => write!(f, "not8 {}", l1),
            Instruction::Not16 { l1 } => write!(f, "not16 {}", l1),
            Instruction::Not32 { l1 } => write!(f, "not32 {}", l1),
            Instruction::Not64 { l1 } => write!(f, "not64 {}", l1),
            Instruction::PowF32 { l1, l2 } => write!(f, "powf32 {}, {}", l1, l2),
            Instruction::PowF64 { l1, l2 } => write!(f, "powf64 {}, {}", l1, l2),
            Instruction::Shl8 { l1, l2 } => write!(f, "shl8 {}, {}", l1, l2),
            Instruction::Shl16 { l1, l2 } => write!(f, "shl16 {}, {}", l1, l2),
            Instruction::Shl32 { l1, l2 } => write!(f, "shl32 {}, {}", l1, l2),
            Instruction::Shl64 { l1, l2 } => write!(f, "shl64 {}, {}", l1, l2),
            Instruction::Shr8 { l1, l2 } => write!(f, "shr8 {}, {}", l1, l2),
            Instruction::Shr16 { l1, l2 } => write!(f, "shr16 {}, {}", l1, l2),
            Instruction::Shr32 { l1, l2 } => write!(f, "shr32 {}, {}", l1, l2),
            Instruction::Shr64 { l1, l2 } => write!(f, "shr64 {}, {}", l1, l2),
            Instruction::Write8 { op, value } => write!(f, "write8 {}, {}", op, value),
            Instruction::Write16 { op, value } => write!(f, "write16 {}, {}", op, value),
            Instruction::Write32 { op, value } => write!(f, "write32 {}, {}", op, value),
            Instruction::Write64 { op, value } => write!(f, "write64 {}, {}", op, value),
            Instruction::Call { func } => write!(f, "call {}", func),
            Instruction::Mov { src, dest } => write!(f, "mov {}, {}", src, dest),
            Instruction::Syscall { id } => write!(f, "syscall {}", id),
            Instruction::Return => write!(f, "return"),
            Instruction::Jmp { location } => write!(f, "jmp {}", location),
            Instruction::JmpPos { l1, location } => write!(f, "jp {}, {}", l1, location),
            Instruction::JmpNeg { l1, location } => write!(f, "jn {}, {}", l1, location),
            Instruction::JmpZero { l1, location } => write!(f, "jz {}, {}", l1, location),
            Instruction::Cmp { l1, l2 } => write!(f, "cmp {}, {}", l1, l2),
        }
    }
}
