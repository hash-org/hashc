//! IR Lowering stage for lowering specific block structures. This module
//! contains the process for lowering a body block and a loop block. The `match`
//! block lowering logic is complicated enough to warrant its own module which
//! is located in `matches.rs`.
use std::mem;

use hash_ir::{
    ir::{BasicBlock, Place},
    ty::Mutability,
};
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::{Context, ScopeKind},
    tir::{BlockStatement, BlockTerm, LoopTerm, MatchTerm, Term, TermId},
};

use super::{BlockAnd, BlockAndExtend, BodyBuilder, LoopBlockInfo};
use crate::build::unpack;

impl<'tcx> BodyBuilder<'tcx> {
    pub(crate) fn block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        block_term: TermId,
    ) -> BlockAnd<()> {
        let span = self.span_of_term(block_term);

        match *block_term.value() {
            Term::Block(ref body) => self.body_block_into_dest(place, block, body),
            Term::Loop(LoopTerm { inner }) => {
                // Begin the loop block by connecting the previous block
                // and terminating it with a `goto` instruction to this block
                let loop_body = self.control_flow_graph.start_new_block();
                self.control_flow_graph.goto(block, loop_body, span);

                let next_block = self.control_flow_graph.start_new_block();

                self.enter_breakable_block(loop_body, next_block, move |this| {
                    // We need to create a temporary for the blocks return value which is
                    // always going to be `()`
                    let tmp_place = this.make_tmp_unit();

                    let body_block_end = unpack!(this.term_into_dest(tmp_place, loop_body, inner));

                    // In the situation that we have the final statement in the loop, this
                    // block should go back to the start of the loop...
                    if !this.control_flow_graph.is_terminated(body_block_end) {
                        this.control_flow_graph.goto(body_block_end, loop_body, span);
                    }

                    this.reached_terminator = false;
                    next_block.unit()
                })
            }
            Term::Match(MatchTerm { subject, cases, origin }) => {
                self.lower_match_term(place, block, span, subject, cases, origin)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn body_block_into_dest(
        &mut self,
        place: Place,
        mut block: BasicBlock,
        body: &BlockTerm,
    ) -> BlockAnd<()> {
        let BlockTerm { stack_id, statements, expr } = body;

        if self.reached_terminator {
            return block.unit();
        }

        Context::enter_resolved_scope_mut(self, ScopeKind::Stack(*stack_id), |this| {
            // Essentially walk all of the statement in the block, and then set
            // the return type of this block as the last expression, or an empty
            // unit if there is no expression.

            for statement in statements.iter() {
                match *statement.value() {
                    // We need to handle declarations here specifically, otherwise
                    // in order to not have to create a temporary for the declaration
                    // which doesn't make sense because we are just declaring a local(s)
                    BlockStatement::Decl(decl) => {
                        unpack!(block = this.lower_declaration(block, &decl));
                    }
                    BlockStatement::Expr(statement) => {
                        // @@Investigate: do we need to deal with the temporary here?
                        unpack!(
                            block = this.term_into_temp(block, statement, Mutability::Immutable)
                        );
                    }
                }
            }

            // If this block has an expression, we need to deal with it since
            // it might change the destination of this block.
            if !this.reached_terminator {
                unpack!(block = this.term_into_dest(place, block, *expr));
            }
        });

        // we finally reset the reached terminator flag so that we can
        // continue to lower the rest of the program
        self.reached_terminator = false;
        block.unit()
    }

    /// Function that handles the lowering of loop expressions. This function
    /// takes in an inner closure which runs the operation of lowering the
    /// inner body loop,
    pub(crate) fn enter_breakable_block<F>(
        &mut self,
        loop_body: BasicBlock,
        next_block: BasicBlock,
        f: F,
    ) -> BlockAnd<()>
    where
        F: FnOnce(&mut BodyBuilder<'tcx>) -> BlockAnd<()>,
    {
        let block_info = LoopBlockInfo { loop_body, next_block };
        let old_block_info = mem::replace(&mut self.loop_block_info, Some(block_info));

        let normal_exit_block = f(self);

        self.loop_block_info = old_block_info;
        normal_exit_block
    }
}
