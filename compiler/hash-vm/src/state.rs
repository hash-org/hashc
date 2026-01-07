/// Utility structure that represents the given state of a particular VM.
///
/// This is useful for when the VM operations require a higher level of
/// context about the current execution state, i.e. the stack pointer, base
/// pointer, and instruction pointer, etc.
pub struct VMState {
    /// The pointer of the stack.
    pub stack_pointer: usize,

    /// The pointer of the base pointer.
    pub base_pointer: usize,

    /// The instruction pointer.
    pub instruction_pointer: usize,
}
