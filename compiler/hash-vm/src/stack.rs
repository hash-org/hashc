//! Hash Compiler VM stack implementation.
use crate::{
    error::{RuntimeError, RuntimeResult, StackAccessKind},
    state::VMState,
};

/// The [Stack] represents temporary storage for a current function scope
/// to ensure that functions can store data closely to the actual running
/// program.
#[derive(Debug)]
pub struct Stack {
    /// The actual internal data of the stack. Once created, the stack size
    /// cannot be modified.
    data: Vec<u8>,
}

impl Stack {
    /// Create a new stack
    pub fn new(size: usize) -> Self {
        Stack { data: vec![0; size] }
    }

    /// Method that verifies that a particular call to modify the stack storage
    /// is sane and safe.
    pub fn verify_access(
        &self,
        access_kind: StackAccessKind,
        size: u8,
        vm_state: &VMState,
    ) -> RuntimeResult<()> {
        match access_kind {
            StackAccessKind::Pop if vm_state.stack_pointer > (size as usize) => Ok(()),
            StackAccessKind::Push if self.data.len() - vm_state.stack_pointer > (size as usize) => {
                Ok(())
            }
            _ => Err(RuntimeError::StackViolationAccess {
                kind: access_kind,
                size,
                total: self.data.len(),
            }),
        }
    }

    /// Pop the last byte of the stack
    pub fn pop8(&mut self, vm_state: &VMState) -> RuntimeResult<&[u8; 1]> {
        self.verify_access(StackAccessKind::Pop, 1, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        let value = self.data[(stack_pointer - 1)..stack_pointer].try_into().unwrap();

        Ok(value)
    }

    /// Pop the last two bytes of the stack
    pub fn pop16(&mut self, vm_state: &VMState) -> RuntimeResult<&[u8; 2]> {
        self.verify_access(StackAccessKind::Pop, 2, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        let value = self.data[(stack_pointer - 2)..stack_pointer].try_into().unwrap();

        Ok(value)
    }

    pub fn pop32(&mut self, vm_state: &VMState) -> RuntimeResult<&[u8; 4]> {
        self.verify_access(StackAccessKind::Pop, 4, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        let value = self.data[(stack_pointer - 4)..stack_pointer].try_into().unwrap();
        Ok(value)
    }

    /// Pop the last eight bytes of the stack
    pub fn pop64(&mut self, vm_state: &VMState) -> RuntimeResult<&[u8; 8]> {
        self.verify_access(StackAccessKind::Pop, 8, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        let value = self.data[(stack_pointer - 8)..stack_pointer].try_into().unwrap();

        Ok(value)
    }

    /// Push the a byte onto the stack
    pub fn push8(&mut self, value: &[u8; 1], vm_state: &VMState) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 1, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        self.data.splice(stack_pointer..(stack_pointer + 1), value.iter().copied());
        Ok(())
    }

    /// Push the two bytes onto the stack
    pub fn push16(&mut self, value: &[u8; 2], vm_state: &VMState) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 2, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        self.data.splice(stack_pointer..(stack_pointer + 2), value.iter().copied());
        Ok(())
    }

    /// Push the four bytes onto the stack
    pub fn push32(&mut self, value: &[u8; 4], vm_state: &VMState) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 4, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        self.data.splice(stack_pointer..(stack_pointer + 4), value.iter().copied());
        Ok(())
    }

    /// Push the eight bytes onto the stack
    pub fn push64(&mut self, value: &[u8; 8], vm_state: &VMState) -> RuntimeResult<()> {
        self.verify_access(StackAccessKind::Push, 8, vm_state)?;

        let stack_pointer = vm_state.stack_pointer;
        self.data.splice(stack_pointer..(stack_pointer + 8), value.iter().copied());
        Ok(())
    }
}
