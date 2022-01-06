//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

/// Register type, we reserve the first
///
///
///
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Register(u8);

impl Register {
    pub const BASE_POINTER: Register = Register(253);
    pub const STACK_POINTER: Register = Register(254);

    /// The current instruction pointer (RIP)
    pub const INSTRUCTION_POINTER: Register = Register(255);
}

/// The register set
pub struct RegisterSet {
    registers: [[u8; 8]; 256],
}

///
/// This is how {get|set}_register{32|16|8} access the entire register. The functions access
/// the lower X-bytes like so:
///
/// Register
/// XXXXXXXX
///     ^^^^
///     get_register32
///
/// Register
/// XXXXXXXX
///       ^^
///     get_register16
///
/// Register
/// XXXXXXXX
///        ^
///     get_register8
///       
///
impl RegisterSet {
    pub fn set_register64(&mut self, register: Register, value: u64) -> u64 {
        todo!()
    }

    pub fn set_register32(&mut self, register: Register, value: u32) -> u32 {
        todo!()
    }

    pub fn set_register16(&mut self, register: Register, value: u16) -> u16 {
        todo!()
    }

    pub fn set_register8(&mut self, register: Register, value: u8) -> u8 {
        todo!()
    }

    pub fn get_register64(&self, register: Register) -> u64 {
        todo!()
    }

    pub fn get_register32(&self, register: Register) -> u32 {
        todo!()
    }

    pub fn get_register16(&self, register: Register) -> u16 {
        todo!()
    }

    pub fn get_register8(&self, register: Register) -> u8 {
        todo!()
    }
}

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
