//! Hash Compiler VM register related logic.

use std::fmt;

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

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

/// The available register set within the VM. This stores all of the data that
/// the registers may hold for a given VM instance.
#[derive(Debug)]
pub struct RegisterSet {
    pub registers: [[u8; 8]; 256],
}

impl Default for RegisterSet {
    fn default() -> Self {
        Self { registers: [[0; 8]; 256] }
    }
}

impl RegisterSet {
    /// Function to get a [Register] within the [RegisterSet].
    pub fn get_register_8b(&self, register: Register) -> &[u8; 8] {
        &self.registers[register.0 as usize]
    }

    /// Function to get a lower four bytes of a [Register] within the
    /// [RegisterSet].
    pub fn get_register_4b(&self, register: Register) -> &[u8; 4] {
        self.registers[register.0 as usize][4..].try_into().unwrap()
    }

    /// Function to get a lower two bytes of a [Register] within the
    /// [RegisterSet].
    pub fn get_register_2b(&self, register: Register) -> &[u8; 2] {
        self.registers[register.0 as usize][6..].try_into().unwrap()
    }

    /// Function to get a lower byte of a [Register] within the [RegisterSet].
    pub fn get_register_b(&self, register: Register) -> &[u8; 1] {
        self.registers[register.0 as usize][7..].try_into().unwrap()
    }

    /// Function to set a [Register] within the [RegisterSet].
    pub fn set_register_8b(&mut self, register: Register, value: &[u8; 8]) {
        let reg = self.get_register_mut(register);
        reg.copy_from_slice(value);
    }

    /// Function to set the lower four bytes of a [Register] within the
    /// [RegisterSet].
    pub fn set_register_4b(&mut self, register: Register, value: &[u8; 4]) {
        let reg = self.get_register_mut(register);
        reg[4..].copy_from_slice(value);
    }

    /// Function to set the lower two bytes of a [Register] within the
    /// [RegisterSet].
    pub fn set_register_2b(&mut self, register: Register, value: &[u8; 2]) {
        let reg = self.get_register_mut(register);
        reg[6..].copy_from_slice(value);
    }

    /// Function to set the lower byte of a [Register] within the [RegisterSet].
    pub fn set_register_b(&mut self, register: Register, value: &[u8; 1]) {
        let reg = self.get_register_mut(register);
        reg[7] = value[0];
    }

    /// Function to get a mutable reference to a  [Register] within the
    /// [RegisterSet].
    fn get_register_mut(&mut self, register: Register) -> &mut [u8; 8] {
        self.registers.get_mut(register.0 as usize).unwrap()
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

/// Macro to create a new register.
///
/// # Example
/// ```
/// use hash_vm::bytecode::register::Register;
/// let r0 = r!(0);
/// let r1 = r!(1);
/// ```
#[macro_export]
macro_rules! r {
    ($index:expr) => {
        Register::new($index)
    };
}
