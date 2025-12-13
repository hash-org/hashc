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
        reg: Register,
        value: u8,
    },
    /// Write a 16bit literal value to a memory address.
    Write16 {
        reg: Register,
        value: u16,
    },
    /// Write a 32bit literal value to a memory address.
    Write32 {
        reg: Register,
        value: u32,
    },
    /// Write a 64bit literal value to a memory address.
    Write64 {
        reg: Register,
        value: u64,
    },
    /// Call a function at a given address
    Call {
        func: Register,
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
