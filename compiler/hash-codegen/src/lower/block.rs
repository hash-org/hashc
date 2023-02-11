//! Contains logic that lowers Hash IR blocks into the target backend IR
//! blocks.

use hash_ir::ir::BasicBlock;

use super::{BlockStatus, FnBuilder};
use crate::traits::builder::BlockBuilderMethods;

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Get a backend basic block for a [BasicBlock]. This function tries
    /// to avoid creating new basic blocks via the builder if they have already
    /// been creating during the building process. The blocks are saved within
    /// the builder `block_map` field as a mapping of indices between one
    /// and another.
    pub fn maybe_get_codegen_block_id(&mut self, block: BasicBlock) -> Option<Builder::BasicBlock> {
        match self.block_map[block] {
            BlockStatus::UnLowered => {
                // We add a new block to the builder, and then update the block
                // map for the future.
                let block_id =
                    Builder::append_block(self.ctx, self.function, &format!("{block:?}"));
                self.block_map[block] = BlockStatus::Lowered(block_id);
                Some(block_id)
            }
            BlockStatus::Skip => None,
            BlockStatus::Lowered(b) => Some(b),
        }
    }

    /// Get the corresponding backend [BasicBlock] ID for a Hash IR block.
    ///
    /// N.B. If the `block` is marked as [`BlockStatus::Skip`], then this
    /// function will panic.
    pub fn get_codegen_block_id(&mut self, block: BasicBlock) -> Builder::BasicBlock {
        self.maybe_get_codegen_block_id(block).unwrap()
    }

    /// Lower a Hash IR block into a target backend IR block.
    ///
    /// Some backend IRs will not have the same terminators for basic blocks.
    /// For example, if an IR does not consider a "call" as a block
    /// terminator, then this will need to combine the two basic blocks in
    /// order to account for this difference.
    pub fn codegen_block(&mut self, mut block: BasicBlock) {
        // Create or get the basic block id. If we didn't get an `id` then
        // this means that the block can be skipped from being generated.
        let block_id = match self.maybe_get_codegen_block_id(block) {
            Some(b) => b,
            None => return,
        };

        let builder = &mut Builder::build(self.ctx, block_id);
        let body = self.body;

        // Loop until two blocks cannot be merged together.
        loop {
            let block_data = &body.blocks()[block];

            // code generate all the statements within the block
            for statement in &block_data.statements {
                self.codegen_statement(builder, statement);
            }

            // code generate the terminator for the block
            let needs_merging = self.codegen_terminator(builder, block, block_data.terminator());

            if !needs_merging {
                break;
            }

            // Here, we essentially merge the successor into the currently built
            // block. We firstly record in the `block_map` that the successor block
            // does not need code generation since we will do it here.

            let mut successors = block_data.terminator().successors();
            let successor = successors.next().unwrap();

            // verify that we have not yet emitted the successor block
            debug_assert!(matches!(self.block_map[successor], BlockStatus::UnLowered));

            // mark the successor block as skipped
            self.block_map[successor] = BlockStatus::Skip;
            block = successor;
        }
    }
}
