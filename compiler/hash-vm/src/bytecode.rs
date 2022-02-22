//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

/// Register type, we reserve the last 3 [Register] indices (by convention) to
/// store the stack pointer, instruction pointer and the base pointer.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub struct Register(u8);

impl Register {
    /// The current base pointer register (PB)
    pub const BASE_POINTER: Register = Register(253);

    /// The current stack pointer register (SP)
    pub const STACK_POINTER: Register = Register(254);

    /// The current instruction pointer register (RIP)
    pub const INSTRUCTION_POINTER: Register = Register(255);

    pub fn new(index: u8) -> Self {
        Self(index)
    }
}

/// The register set
#[derive(Debug)]
pub struct RegisterSet {
    pub registers: [[u8; 8]; 256],
}

impl Default for RegisterSet {
    fn default() -> Self {
        Self {
            registers: [[0; 8]; 256],
        }
    }
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
    /// Function to get a [Register] within the [RegisterSet]. The inner implementation
    /// uses `unsafe` because a [Register] index cannot be larger than a [u8] and therefore
    /// indexing the [RegisterSet] is always safe as there are always [`u8::MAX`]  number of
    /// registers.
    pub fn get_register_8b(&self, register: Register) -> &[u8; 8] {
        &self.registers[register.0 as usize]
    }

    pub fn get_register_4b(&self, register: Register) -> &[u8; 4] {
        self.registers[register.0 as usize][4..].try_into().unwrap()
    }

    pub fn get_register_2b(&self, register: Register) -> &[u8; 2] {
        self.registers[register.0 as usize][6..].try_into().unwrap()
    }

    pub fn get_register_b(&self, register: Register) -> &[u8; 1] {
        self.registers[register.0 as usize][7..].try_into().unwrap()
    }

    pub fn set_register_8b(&mut self, register: Register, value: &[u8; 8]) {
        let reg = self.get_register_mut(register);
        reg.copy_from_slice(value);
    }

    pub fn set_register_4b(&mut self, register: Register, value: &[u8; 4]) {
        let reg = self.get_register_mut(register);
        reg[4..].copy_from_slice(value);
    }

    pub fn set_register_2b(&mut self, register: Register, value: &[u8; 2]) {
        let reg = self.get_register_mut(register);
        reg[6..].copy_from_slice(value);
    }

    pub fn set_register_b(&mut self, register: Register, value: &[u8; 1]) {
        let reg = self.get_register_mut(register);
        reg[7] = value[0];
    }

    /// Function to get a mutable reference to a  [Register] within the [RegisterSet].
    fn get_register_mut(&mut self, register: Register) -> &mut [u8; 8] {
        unsafe { self.registers.get_unchecked_mut(register.0 as usize) }
    }

    /// Set the bytes of a register.
    pub fn set_register64(&mut self, register: Register, value: u64) {
        let reg = self.get_register_mut(register);

        reg.copy_from_slice(&value.to_be_bytes());
    }

    /// Set the bytes of a register using a float.
    pub fn set_register_f64(&mut self, register: Register, value: f64) {
        let reg = self.get_register_mut(register);

        reg.copy_from_slice(&value.to_be_bytes());
    }

    /// Set the lower four bytes of a register using a float.
    pub fn set_register_f32(&mut self, register: Register, value: f32) {
        let reg = self.get_register_mut(register);

        reg[4..].copy_from_slice(&value.to_be_bytes());
    }

    /// Set the lower four bytes of a register.
    pub fn set_register32(&mut self, register: Register, value: u32) {
        let reg = self.get_register_mut(register);

        reg[4..].copy_from_slice(&value.to_be_bytes());
    }

    /// Set the lower two bytes of a register.
    pub fn set_register16(&mut self, register: Register, value: u16) {
        let reg = self.get_register_mut(register);

        reg[6..].copy_from_slice(&value.to_be_bytes());
    }

    /// Set the lower byte of a register.
    pub fn set_register8(&mut self, register: Register, value: u8) {
        let reg = self.get_register_mut(register);
        reg[7] = value;
    }

    /// Get a register.
    pub fn get_register_f64(&self, register: Register) -> f64 {
        let reg = self.get_register_8b(register);
        f64::from_be_bytes(*reg)
    }

    /// Get the lower four bytes of a register.
    pub fn get_register_f32(&self, register: Register) -> f32 {
        let reg = self.get_register_8b(register);
        f32::from_be_bytes(reg[4..].try_into().unwrap())
    }

    /// Get a register.
    pub fn get_register64(&self, register: Register) -> u64 {
        let reg = self.get_register_8b(register);
        u64::from_be_bytes(*reg)
    }

    /// Get the lower four bytes of a register.
    pub fn get_register32(&self, register: Register) -> u32 {
        let reg = self.get_register_8b(register);
        u32::from_be_bytes(reg[4..].try_into().unwrap())
    }

    /// Get the lower two bytes of a register.
    pub fn get_register16(&self, register: Register) -> u16 {
        let reg = self.get_register_8b(register);
        u16::from_be_bytes(reg[6..].try_into().unwrap())
    }

    /// Get the lower byte of a register.
    pub fn get_register8(&self, register: Register) -> u8 {
        let reg = self.get_register_8b(register);
        reg[7]
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
