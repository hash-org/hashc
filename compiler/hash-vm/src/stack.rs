//! Hash Compiler VM stack implementation.
use crate::error::{RuntimeError, RuntimeResult, StackAccessKind};

/// The [Stack] represents temporary storage for a current function scope
/// to ensure that functions can store data closely to the actual running
/// program.
#[derive(Debug)]
pub struct Stack {
    /// The actual internal data of the stack. Once created, the stack size
    /// cannot be modified.
    data: Vec<u8>,
    /// The internal representation of where the stack offset is located at.
    stack_pointer: usize,
}

impl Stack {
    /// Create a new stack
    pub fn new(size: usize) -> Self {
        Stack { data: vec![0; size], stack_pointer: 0 }
    }

    /// Method that verifies that a particular call to modify the stack storage
    /// is sane and safe.
    pub fn verify_access(&self, access_kind: StackAccessKind, size: u8) -> RuntimeResult<()> {
        match access_kind {
            StackAccessKind::Pop if self.stack_pointer > size.into() => Ok(()),
            StackAccessKind::Push if self.data.len() - self.stack_pointer > size.into() => Ok(()),
            _ => Err(RuntimeError::StackViolationAccess {
                kind: access_kind,
                size,
                total: self.data.len(),
            }),
        }
    }

    /// Pop the last byte of the stack
    pub fn pop8(&mut self) -> RuntimeResult<&[u8; 1]> {
        self.verify_access(StackAccessKind::Pop, 1)?;

        let value = (&self.data[(self.stack_pointer - 1)..self.stack_pointer]).try_into().unwrap();
        self.stack_pointer -= 1;

        Ok(value)
    }

    /// Pop the last two bytes of the stack
    pub fn pop16(&mut self) -> RuntimeResult<&[u8; 2]> {
        self.verify_access(StackAccessKind::Pop, 2)?;

        let value = (&self.data[(self.stack_pointer - 2)..self.stack_pointer]).try_into().unwrap();
        self.stack_pointer -= 2;

        Ok(value)
    }

    pub fn pop32(&mut self) -> RuntimeResult<&[u8; 4]> {
        self.verify_access(StackAccessKind::Pop, 4)?;

        let value = (&self.data[(self.stack_pointer - 4)..self.stack_pointer]).try_into().unwrap();
        self.stack_pointer -= 4;

        Ok(value)
    }

    /// Pop the last eight bytes of the stack
    pub fn pop64(&mut self) -> RuntimeResult<&[u8; 8]> {
        self.verify_access(StackAccessKind::Pop, 8)?;

        let value = (&self.data[(self.stack_pointer - 8)..self.stack_pointer]).try_into().unwrap();
        self.stack_pointer -= 8;

        Ok(value)
    }

    /// Push the a byte onto the stack
    pub fn push8(&mut self, value: &[u8; 1]) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 1)?;

        self.data.splice(self.stack_pointer..(self.stack_pointer + 1), value.iter().copied());
        self.stack_pointer += 1;
        Ok(())
    }

    /// Push the two bytes onto the stack
    pub fn push16(&mut self, value: &[u8; 2]) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 2)?;

        self.data.splice(self.stack_pointer..(self.stack_pointer + 2), value.iter().copied());
        self.stack_pointer += 2;
        Ok(())
    }

    /// Push the four bytes onto the stack
    pub fn push32(&mut self, value: &[u8; 4]) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 4)?;

        self.data.splice(self.stack_pointer..(self.stack_pointer + 4), value.iter().copied());
        self.stack_pointer += 4;
        Ok(())
    }

    /// Push the eight bytes onto the stack
    pub fn push64(&mut self, value: &[u8; 8]) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 8)?;

        self.data.splice(self.stack_pointer..(self.stack_pointer + 8), value.iter().copied());
        self.stack_pointer += 8;
        Ok(())
    }
}
