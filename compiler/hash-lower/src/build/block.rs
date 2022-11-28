//! IR Lowering stage for lowering specific block structures. This module
//! contains the process for lowering a body block and a loop block. The `match`
//! block lowering logic is complicated enough to warrant its own module which
//! is located in `matches.rs`.
use std::mem;

use hash_ast::ast::{AstNodeRef, Block, BodyBlock, Expr, LoopBlock};
use hash_ir::{
    ir::{BasicBlock, Place},
    ty::Mutability,
};

use super::{BlockAnd, BlockAndExtend, Builder, LoopBlockInfo};
use crate::build::unpack;

impl<'tcx> Builder<'tcx> {
    pub(crate) fn block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        ast_block: AstNodeRef<'tcx, Block>,
    ) -> BlockAnd<()> {
        let span = ast_block.span();

        match ast_block.body {
            Block::Body(body) => {
                self.with_scope(ast_block, |this| this.body_block_into_dest(place, block, body))
            }

            // Send this off into the `match` lowering logic
            Block::Match(..) => todo!(),

            Block::Loop(LoopBlock { contents }) => {
                // Begin the loop block by connecting the previous block
                // and terminating it with a `goto` instruction to this block
                let loop_body = self.control_flow_graph.start_new_block();
                self.control_flow_graph.goto(block, loop_body, span);

                let next_block = self.control_flow_graph.start_new_block();

                self.enter_breakable_block(loop_body, next_block, place, move |this| {
                    // We need to create a temporary for the blocks return value which is
                    // always going to be `()`
                    let tmp_place = this.make_tmp_unit();

                    let body_block_end =
                        unpack!(this.block_into_dest(tmp_place, loop_body, contents.ast_ref()));

                    // In the situation that we have the final statement in the loop, this
                    // block should go back to the start of the loop...
                    if !this.control_flow_graph.is_terminated(body_block_end) {
                        this.control_flow_graph.goto(body_block_end, loop_body, ast_block.span());
                    }

                    next_block.unit()
                })
            }

            // These variants are removed during the de-sugaring stage
            Block::For(..) | Block::While(..) | Block::If(..) => unreachable!(),

            // Lowering implementation blocks is a no-op because this is dealt with
            // at a higher level, so we just want to skip this.
            Block::Impl(..) | Block::Mod(..) => block.unit(),
        }
    }

    pub(crate) fn body_block_into_dest(
        &mut self,
        place: Place,
        mut block: BasicBlock,
        body: &'tcx BodyBlock,
    ) -> BlockAnd<()> {
        // Essentially walk all of the statement in the block, and then set
        // the return type of this block as the last expression, or an empty
        // unit if there is no expression.
        for statement in body.statements.iter() {
            if self.reached_terminator {
                break;
            }

            // We need to handle declarations here specifically, otherwise
            // in order to not have to create a temporary for the declaration
            // which doesn't make sense because we are just declaring a local(s)
            if let Expr::Declaration(decl) = statement.body() {
                unpack!(block = self.handle_expr_declaration(block, decl));
            } else {
                // @@Investigate: do we need to deal with the temporary here?
                unpack!(
                    block = self.expr_into_temp(block, statement.ast_ref(), Mutability::Immutable)
                );
            }
        }

        // If this block has an expression, we need to deal with it since
        // it might change the destination of this block.
        if let Some(expr) = body.expr.as_ref() && !self.reached_terminator {
            unpack!(block = self.expr_into_dest(place, block, expr.ast_ref()));
        }

        block.unit()
    }

    /// Function that handles the lowering of loop expressions. This function
    /// takes in an inner closure which runs the operation of lowering the
    /// inner body loop,
    pub(crate) fn enter_breakable_block<F>(
        &mut self,
        loop_body: BasicBlock,
        next_block: BasicBlock,
        _break_destination: Place,
        f: F,
    ) -> BlockAnd<()>
    where
        F: FnOnce(&mut Builder<'tcx>) -> BlockAnd<()>,
    {
        let block_info = LoopBlockInfo { loop_body, next_block };
        let old_block_info = mem::replace(&mut self.loop_block_info, Some(block_info));

        let normal_exit_block = f(self);

        self.loop_block_info = old_block_info;
        normal_exit_block
    }
}
