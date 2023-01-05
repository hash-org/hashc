//! Contains logic that lowers Hash IR blocks into the target backend IR
//! blocks.

use hash_ir::ir::BasicBlock;

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Lower a Hash IR block into a target backend IR block.
    pub fn codegen_block(&mut self, _block: BasicBlock) {
        todo!()
    }
}
