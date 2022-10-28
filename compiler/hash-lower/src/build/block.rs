//! IR Lowering stage for lowering specific block structures. This module
//! contains the process for lowering a body block and a loop block. The `match`
//! block lowering logic is complicated enough to warrant its own module which
//! is located in `matches.rs`.
use hash_ast::ast::{AstNodeRef, Block, BodyBlock};
use hash_ir::ir::{BasicBlock, Place};

use super::{BlockAnd, BlockAndExtend, Builder};

impl<'a, 'tcx> Builder<'a, 'tcx> {
    pub(crate) fn block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        body: AstNodeRef<'a, Block>,
    ) -> BlockAnd<()> {
        // Check which kind of block we are dealing with...
        match body.body {
            Block::Body(body) => self.body_block_into_dest(place, block, body),

            // Send this off into the `match` lowering logic
            Block::Match(..) => todo!(),

            // Send this off into the `loop` lowering logic
            Block::Loop(..) => todo!(),

            // These variants are removed during the de-sugaring stage
            Block::For(..) | Block::While(..) | Block::If(..) => unreachable!(),

            // Lowering implementation blocks is a no-op because this is dealt with
            // at a lower level, so we just want to skip this.
            Block::Impl(..) | Block::Mod(..) => block.unit(),
        }
    }

    pub(crate) fn body_block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        body: &BodyBlock,
    ) -> BlockAnd<()> {
        // Essentially walk all of the statement in the block, and then set
        // the return type of this block as the last expression, or an empty
        // unit if there is no expression.
        for statement in body.statements.iter() {}

        // If this block has an expression, we need to deal with it since
        // it might change the destination of this block.
        if let Some(expr) = body.expr.as_ref() {}

        block.unit()
    }
}
