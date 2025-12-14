use std::fmt;

use hash_utils::index_vec::Idx;

use super::register::{Register, RegisterSet};

/// A 24-bit label offset, representing an instruction offset within a function.
/// This allows for up to 16,777,215 instructions per function while saving
/// memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LabelOffset([u8; 3]);

impl LabelOffset {
    /// The maximum value that can be represented in 24 bits.
    pub const MAX: usize = 0x00FF_FFFF;

    /// Create a new `LabelOffset` from a `usize`.
    ///
    /// # Panics
    /// Panics if `offset` exceeds 24-bit range (16,777,215).
    pub fn new(offset: usize) -> Self {
        assert!(offset <= Self::MAX, "offset {} exceeds 24-bit range (max: {})", offset, Self::MAX);
        Self([(offset & 0xFF) as u8, ((offset >> 8) & 0xFF) as u8, ((offset >> 16) & 0xFF) as u8])
    }

    /// Try to create a new `LabelOffset` from a `usize`.
    /// Returns `None` if the offset exceeds 24-bit range.
    pub fn try_new(offset: usize) -> Option<Self> {
        if offset <= Self::MAX {
            Some(Self([
                (offset & 0xFF) as u8,
                ((offset >> 8) & 0xFF) as u8,
                ((offset >> 16) & 0xFF) as u8,
            ]))
        } else {
            None
        }
    }

    /// Get the offset value as a `usize`.
    pub fn get(self) -> usize {
        self.0[0] as usize | ((self.0[1] as usize) << 8) | ((self.0[2] as usize) << 16)
    }
}

/// Implement the `Idx` trait to allow `LabelOffset` to be used with `IndexVec`.
impl Idx for LabelOffset {
    fn from_usize(idx: usize) -> Self {
        Self::new(idx)
    }

    fn index(self) -> usize {
        self.get()
    }
}

impl fmt::Display for LabelOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

/// A type that can either be a [Register] or a [LabelOffset].
///
/// This is used in instructions that can take either a register or a label
/// as an argument, such as jump instructions.
///
/// This is used to initially represent the instruction before it is resolved
/// into a concrete instruction with only registers (after label resolution).
/// When the function body is finalised, all [LabelOffset]s will be replaced
/// with the corresponding [Register]s that hold the instruction addresses.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operand {
    /// A register operand.
    Register(Register),

    /// A label offset within the function body.
    Label(LabelOffset),

    /// Literal immediate value.
    Immediate(usize),
}

impl Operand {
    /// Check if the operand is a register.
    pub fn is_register(&self) -> bool {
        matches!(self, Operand::Register(_))
    }

    /// Check if the operand is a label.
    pub fn is_label(&self) -> bool {
        matches!(self, Operand::Label(_))
    }

    /// Check if the operand is an immediate value.
    pub fn is_immediate(&self) -> bool {
        matches!(self, Operand::Immediate(_))
    }

    pub fn as_literal_usize(&self, registers: &RegisterSet) -> usize {
        match self {
            Operand::Register(reg) => {
                let reg_value = registers.get_register64(*reg);
                reg_value as usize
            }
            Operand::Immediate(value) => *value,
            Operand::Label(_) => panic!("Cannot convert label operand to literal usize"),
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Register(reg) => write!(f, "{}", reg),
            Operand::Label(label) => write!(f, "${}", label),
            Operand::Immediate(value) => write!(f, "#{}", value),
        }
    }
}
