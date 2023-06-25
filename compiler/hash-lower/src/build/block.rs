//! IR Lowering stage for lowering specific block structures. This module
//! contains the process for lowering a body block and a loop block. The `match`
//! block lowering logic is complicated enough to warrant its own module which
//! is located in `matches.rs`.
use std::mem;

use hash_ast::ast::MatchOrigin;
use hash_ir::{
    ir::{BasicBlock, Place},
    ty::Mutability,
};
use hash_tir::{
    context::ScopeKind,
    control::{LoopTerm, MatchTerm},
    environment::env::AccessToEnv,
    scopes::BlockTerm,
    terms::{Term, TermId},
    utils::context::ContextUtils,
};
use hash_utils::store::{CloneStore, SequenceStore};

use super::{BlockAnd, BlockAndExtend, BodyBuilder, LoopBlockInfo};
use crate::build::unpack;

impl<'tcx> BodyBuilder<'tcx> {
    pub(crate) fn block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        block_term_id: TermId,
    ) -> BlockAnd<()> {
        let span = self.span_of_term(block_term_id);
        let block_term = self.stores().term().get(block_term_id);

        match &block_term {
            Term::Block(ref body) => self.body_block_into_dest(place, block, body),
            Term::Loop(LoopTerm { block: ref body }) => {
                // Begin the loop block by connecting the previous block
                // and terminating it with a `goto` instruction to this block
                let loop_body = self.control_flow_graph.start_new_block();
                self.control_flow_graph.goto(block, loop_body, span);

                let next_block = self.control_flow_graph.start_new_block();

                self.enter_breakable_block(loop_body, next_block, move |this| {
                    // We need to create a temporary for the blocks return value which is
                    // always going to be `()`
                    let tmp_place = this.make_tmp_unit();

                    let body_block_end =
                        unpack!(this.body_block_into_dest(tmp_place, loop_body, body));

                    // In the situation that we have the final statement in the loop, this
                    // block should go back to the start of the loop...
                    if !this.control_flow_graph.is_terminated(body_block_end) {
                        this.control_flow_graph.goto(body_block_end, loop_body, span);
                    }

                    next_block.unit()
                })
            }
            Term::Match(MatchTerm { subject, cases }) => {
                // @@TodoTIR: we should be able to get the origin from the
                // match term.
                let origin = MatchOrigin::Match;
                self.lower_match_term(place, block, span, *subject, *cases, origin)
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
        let BlockTerm { stack_id, statements, return_value } = body;

        if self.reached_terminator {
            return block.unit();
        }

        ContextUtils::<'_>::enter_resolved_scope_mut(self, ScopeKind::Stack(*stack_id), |this| {
            // Essentially walk all of the statement in the block, and then set
            // the return type of this block as the last expression, or an empty
            // unit if there is no expression.
            let statements = this.stores().term_list().get_vec(*statements);

            for statement_id in statements {
                let statement = this.stores().term().get(statement_id);
                match statement {
                    // We need to handle declarations here specifically, otherwise
                    // in order to not have to create a temporary for the declaration
                    // which doesn't make sense because we are just declaring a local(s)
                    Term::Decl(decl) => {
                        let span = this.span_of_term(statement_id);
                        unpack!(block = this.lower_declaration(block, &decl, span));
                    }
                    _ => {
                        // @@Investigate: do we need to deal with the temporary here?
                        unpack!(
                            block = this.term_into_temp(block, statement_id, Mutability::Immutable)
                        );
                    }
                }
            }

            // If this block has an expression, we need to deal with it since
            // it might change the destination of this block.
            if !this.reached_terminator {
                unpack!(block = this.term_into_dest(place, block, *return_value));
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
