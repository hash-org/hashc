//! Function builder related logic for the Hash VM.

use hash_repr::ty::InstanceId;
use hash_utils::index_vec::IndexVec;

use crate::bytecode::{Instruction, op::LabelOffset, pretty::FunctionBody};

/// Represents a single basic block with its instructions.
#[derive(Debug, Clone)]
struct Block {
    /// The instructions within this block.
    instructions: Vec<Instruction>,
}

impl Block {
    /// Create a new empty block.
    fn new() -> Self {
        Self { instructions: Vec::new() }
    }

    /// Append an instruction to this block.
    fn emit(&mut self, instruction: Instruction) {
        self.instructions.push(instruction);
    }

    /// Append multiple instructions to this block.
    fn append(&mut self, instructions: Vec<Instruction>) {
        self.instructions.extend(instructions);
    }
}

/// The [FunctionBuilder] allows building functions with [Block]s that can be
/// constructed out of order. Instructions can be appended to any block at any
/// time. Once building is complete, call [FunctionBuilder::consolidate] to
/// merge all blocks into the final instruction stream with resolved label
/// offsets.
#[derive(Debug)]
pub struct FunctionBuilder {
    /// The ABI of the function, this is used to generate
    /// the correct instructions for the function, to read the
    /// arguments and return values correctly.
    pub instance: InstanceId,

    /// The basic blocks of the function. Each block has its own instruction
    /// buffer, allowing out-of-order construction where instructions can be
    /// appended to any block at any time.
    blocks: IndexVec<LabelOffset, Block>,

    /// The current active block. Instructions emitted via `emit()` or
    /// `append()` without specifying a block will go to this block.
    current_block: Option<LabelOffset>,

    /// Whether the function has been consolidated. Once consolidated, the
    /// function is immutable and blocks can no longer be modified.
    consolidated: bool,

    /// The consolidated body of the function after `consolidate()` is called.
    /// This contains all instructions from all blocks in order.
    body: IndexVec<LabelOffset, Instruction>,

    /// The final label positions after consolidation. This maps each block's
    /// label to its actual instruction offset in the consolidated body:
    ///
    ///  Block 0 (LabelOffset(0)) -> Instruction offset 0
    ///  Block 1 (LabelOffset(1)) -> Instruction offset 5
    ///  Block 2 (LabelOffset(2)) -> Instruction offset 12
    ///  ...
    labels: IndexVec<LabelOffset, LabelOffset>,
}

impl FunctionBuilder {
    /// Create a new [FunctionBuilder] with the given instance.
    pub fn new(instance: InstanceId) -> Self {
        Self {
            instance,
            blocks: IndexVec::new(),
            current_block: None,
            consolidated: false,
            body: IndexVec::new(),
            labels: IndexVec::new(),
        }
    }

    /// Reserve a new basic block and return its label.
    /// The block starts empty and instructions can be added to it later.
    pub fn reserve_block(&mut self) -> LabelOffset {
        assert!(!self.consolidated, "cannot reserve blocks after consolidation");
        let label = self.blocks.push(Block::new());

        // If this is the first block, make it current
        if self.current_block.is_none() {
            self.current_block = Some(label);
        }

        label
    }

    /// Switch the current active block to the specified block.
    /// Subsequent calls to `emit()` or `append()` will add instructions to this
    /// block.
    pub fn switch_to_block(&mut self, block: LabelOffset) {
        assert!(!self.consolidated, "cannot switch blocks after consolidation");
        assert!(self.blocks.get(block).is_some(), "block {:?} does not exist", block);
        self.current_block = Some(block);
    }

    /// Get the currently active block, if any.
    pub fn current_block(&self) -> Option<LabelOffset> {
        self.current_block
    }

    /// Emit a single instruction to the current active block.
    ///
    /// # Panics
    /// Panics if no block is currently active or if the function has been
    /// consolidated.
    pub fn emit(&mut self, instruction: Instruction) {
        assert!(!self.consolidated, "cannot emit instructions after consolidation");
        let block = self.current_block.expect("no active block");
        self.blocks[block].emit(instruction);
    }

    /// Append multiple instructions to the current active block.
    ///
    /// # Panics
    /// Panics if no block is currently active or if the function has been
    /// consolidated.
    pub fn append(&mut self, instructions: Vec<Instruction>) {
        assert!(!self.consolidated, "cannot append instructions after consolidation");
        let block = self.current_block.expect("no active block");
        self.blocks[block].append(instructions);
    }

    /// Emit a single instruction to a specific block.
    pub fn emit_to_block(&mut self, block: LabelOffset, instruction: Instruction) {
        assert!(!self.consolidated, "cannot emit instructions after consolidation");
        assert!(self.blocks.get(block).is_some(), "block {:?} does not exist", block);
        self.blocks[block].emit(instruction);
    }

    /// Append multiple instructions to a specific block.
    pub fn append_to_block(&mut self, block: LabelOffset, instructions: Vec<Instruction>) {
        assert!(!self.consolidated, "cannot append instructions after consolidation");
        assert!(self.blocks.get(block).is_some(), "block {:?} does not exist", block);
        self.blocks[block].append(instructions);
    }

    /// Consolidate all blocks into the final instruction stream.
    /// This resolves all label offsets to their actual positions in the
    /// instruction stream.
    ///
    /// After consolidation, the function becomes immutable and no more
    /// instructions can be added.
    ///
    /// # Panics
    /// Panics if the function has already been consolidated.
    pub fn consolidate(&mut self) {
        assert!(!self.consolidated, "function has already been consolidated");

        self.body = IndexVec::new();
        self.labels = IndexVec::new();

        // Iterate through all blocks in order and merge their instructions
        for (_block_label, block) in self.blocks.iter_enumerated() {
            // Record the current offset as the label position for this block
            let offset = LabelOffset::new(self.body.len());
            self.labels.push(offset);

            // Append all instructions from this block
            self.body.extend(block.instructions.iter().copied());
        }

        self.consolidated = true;
    }

    /// Check if the function has been consolidated.
    pub fn is_consolidated(&self) -> bool {
        self.consolidated
    }

    /// Get the number of blocks in the function.
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }

    /// Get a reference to the consolidated instruction body.
    ///
    /// # Panics
    /// Panics if the function has not been consolidated yet.
    pub fn body(&self) -> &IndexVec<LabelOffset, Instruction> {
        assert!(self.consolidated, "function must be consolidated before accessing body");
        &self.body
    }

    /// Get a reference to the label offset mappings.
    ///
    /// # Panics
    /// Panics if the function has not been consolidated yet.
    pub fn label_offsets(&self) -> &IndexVec<LabelOffset, LabelOffset> {
        assert!(self.consolidated, "function must be consolidated before accessing labels");
        &self.labels
    }
}

impl FunctionBody for FunctionBuilder {
    fn labels(&self) -> &IndexVec<LabelOffset, LabelOffset> {
        &self.labels
    }

    fn instructions(&self) -> &IndexVec<LabelOffset, Instruction> {
        &self.body
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::{Instruction, register::Register};

    // Helper to create a dummy InstanceId for testing
    fn dummy_instance() -> InstanceId {
        unsafe { std::mem::zeroed() }
    }

    #[test]
    fn test_out_of_order_block_building() {
        let instance = dummy_instance();
        let mut builder = FunctionBuilder::new(instance);

        // Create three blocks
        let block0 = builder.reserve_block();
        let block1 = builder.reserve_block();
        let block2 = builder.reserve_block();

        // Add instructions out of order
        builder.switch_to_block(block1);
        builder.emit(Instruction::Add32 { l1: Register::new(1), l2: Register::new(2) });

        builder.switch_to_block(block0);
        builder.emit(Instruction::Add64 { l1: Register::new(0), l2: Register::new(1) });

        builder.switch_to_block(block2);
        builder.emit(Instruction::Sub32 { l1: Register::new(3), l2: Register::new(4) });

        // Add more instructions to block0 after working on other blocks
        builder.switch_to_block(block0);
        builder.emit(Instruction::Mul32 { l1: Register::new(5), l2: Register::new(6) });

        // Consolidate
        builder.consolidate();

        // Verify the final instruction order
        let body = builder.body();
        assert_eq!(body.len(), 4);

        // Block 0 should have 2 instructions at offset 0
        assert_eq!(builder.label_offsets()[block0].get(), 0);

        // Block 1 should have 1 instruction at offset 2
        assert_eq!(builder.label_offsets()[block1].get(), 2);

        // Block 2 should have 1 instruction at offset 3
        assert_eq!(builder.label_offsets()[block2].get(), 3);
    }

    #[test]
    fn test_append_to_specific_block() {
        let instance = dummy_instance();
        let mut builder = FunctionBuilder::new(instance);

        let block0 = builder.reserve_block();
        let block1 = builder.reserve_block();

        // Use append_to_block instead of switching
        builder.append_to_block(
            block1,
            vec![
                Instruction::Add32 { l1: Register::new(1), l2: Register::new(2) },
                Instruction::Sub32 { l1: Register::new(3), l2: Register::new(4) },
            ],
        );

        builder.append_to_block(
            block0,
            vec![Instruction::Add64 { l1: Register::new(0), l2: Register::new(1) }],
        );

        builder.consolidate();

        let body = builder.body();
        assert_eq!(body.len(), 3);
        assert_eq!(builder.label_offsets()[block0].get(), 0);
        assert_eq!(builder.label_offsets()[block1].get(), 1);
    }
}
