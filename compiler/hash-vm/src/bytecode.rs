//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::register::Register;

/// An instruction
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Instruction {
    Pop8 {
        l1: Register,
    },
    Pop16 {
        l1: Register,
    },
    Pop32 {
        l1: Register,
    },
    Pop64 {
        l1: Register,
    },
    Push8 {
        l1: Register,
    },
    Push16 {
        l1: Register,
    },
    Push32 {
        l1: Register,
    },
    Push64 {
        l1: Register,
    },
    Add8 {
        l1: Register,
        l2: Register,
    },
    Sub8 {
        l1: Register,
        l2: Register,
    },
    Div8 {
        l1: Register,
        l2: Register,
    },
    Mul8 {
        l1: Register,
        l2: Register,
    },
    Mod8 {
        l1: Register,
        l2: Register,
    },
    Add16 {
        l1: Register,
        l2: Register,
    },
    Sub16 {
        l1: Register,
        l2: Register,
    },
    Div16 {
        l1: Register,
        l2: Register,
    },
    Mul16 {
        l1: Register,
        l2: Register,
    },
    Mod16 {
        l1: Register,
        l2: Register,
    },
    Add32 {
        l1: Register,
        l2: Register,
    },
    Sub32 {
        l1: Register,
        l2: Register,
    },
    Div32 {
        l1: Register,
        l2: Register,
    },
    Mul32 {
        l1: Register,
        l2: Register,
    },
    Mod32 {
        l1: Register,
        l2: Register,
    },
    Add64 {
        l1: Register,
        l2: Register,
    },
    Sub64 {
        l1: Register,
        l2: Register,
    },
    Div64 {
        l1: Register,
        l2: Register,
    },
    Mul64 {
        l1: Register,
        l2: Register,
    },
    Mod64 {
        l1: Register,
        l2: Register,
    },

    IDiv8 {
        l1: Register,
        l2: Register,
    },
    IMul8 {
        l1: Register,
        l2: Register,
    },
    IDiv16 {
        l1: Register,
        l2: Register,
    },
    IMul16 {
        l1: Register,
        l2: Register,
    },
    IDiv32 {
        l1: Register,
        l2: Register,
    },
    IMul32 {
        l1: Register,
        l2: Register,
    },
    IDiv64 {
        l1: Register,
        l2: Register,
    },
    IMul64 {
        l1: Register,
        l2: Register,
    },
    AddF32 {
        l1: Register,
        l2: Register,
    },
    SubF32 {
        l1: Register,
        l2: Register,
    },
    DivF32 {
        l1: Register,
        l2: Register,
    },
    MulF32 {
        l1: Register,
        l2: Register,
    },
    ModF32 {
        l1: Register,
        l2: Register,
    },
    AddF64 {
        l1: Register,
        l2: Register,
    },
    SubF64 {
        l1: Register,
        l2: Register,
    },
    DivF64 {
        l1: Register,
        l2: Register,
    },
    MulF64 {
        l1: Register,
        l2: Register,
    },
    ModF64 {
        l1: Register,
        l2: Register,
    },
    /// Logical Exclusive OR
    Xor {
        l1: Register,
        l2: Register,
    },
    /// Logical OR
    Or {
        l1: Register,
        l2: Register,
    },
    /// Logical AND (Like there exists a Non-Logical and)
    And {
        l1: Register,
        l2: Register,
    },
    Not {
        l1: Register,
    },

    /// We don't have integer variants as there is no need for them
    PowF32 {
        l1: Register,
        l2: Register,
    },
    PowF64 {
        l1: Register,
        l2: Register,
    },

    Shl8 {
        l1: Register,
        l2: Register,
    },
    Shr8 {
        l1: Register,
        l2: Register,
    },
    Shl16 {
        l1: Register,
        l2: Register,
    },
    Shr16 {
        l1: Register,
        l2: Register,
    },
    Shl32 {
        l1: Register,
        l2: Register,
    },
    Shr32 {
        l1: Register,
        l2: Register,
    },
    Shl64 {
        l1: Register,
        l2: Register,
    },
    Shr64 {
        l1: Register,
        l2: Register,
    },
    /// Call a function at a given address?
    Call {
        func: Register,
    },
    /// Copy a value from source register to destination register.
    Mov {
        src: Register,
        dest: Register,
    },
    Syscall {
        id: Register,
    },
    Return,

    /// The jump family (jumpin' around the christmas tree)
    Jmp {
        location: Register,
    },
    JmpPos {
        l1: Register,
        location: Register,
    },
    JmpNeg {
        l1: Register,
        location: Register,
    },
    JmpZero {
        l1: Register,
        location: Register,
    },
    // Compare both values and store the result in `l1`
    Cmp {
        l1: Register,
        l2: Register,
    },
}
