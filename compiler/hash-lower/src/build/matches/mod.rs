//! Module that contains all of the logic with dealing with `match` blocks.
//! Lowering `match` blocks is probably the most complex part of lowering, since
//! we have to create essentially a *jump* table each case that is specified in
//! the `match` arms, which might also have `if` guards, `or` patterns, etc.
#![allow(unused, dead_code)]

use std::mem;

use hash_ast::ast::{AstNodeRef, AstNodes, Expr, MatchCase};
use hash_ir::{
    ir::{BasicBlock, Place, TerminatorKind},
    ty::Mutability,
};
use hash_source::location::Span;
use hash_types::pats::{Pat, PatId};
use hash_utils::{stack::ensure_sufficient_stack, store::Store};

use self::candidate::{Candidate, Candidates};
use super::{place::PlaceBuilder, unpack, BlockAnd, BlockAndExtend, Builder};

mod candidate;
mod test;

impl<'tcx> Builder<'tcx> {
    /// This is the entry point of matching an expression. Firstly, we deal with
    /// the subject of the match, and then we build a decision tree of all
    /// of the arms that have been specified, then we create all of the
    /// blocks that are required to represent the decision tree. After the
    /// decision tree has been built, we then build the blocks
    /// that are required to represent the actual match arms.
    pub(crate) fn match_expr(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        span: Span,
        subject: AstNodeRef<'tcx, Expr>,
        arms: &'tcx AstNodes<MatchCase>,
    ) -> BlockAnd<()> {
        let subject_place =
            unpack!(block = self.as_place_builder(block, subject, Mutability::Immutable));

        // Make the decision tree here...
        let mut arm_candidates = self.create_match_candidates(&subject_place, arms);

        let mut candidates =
            arm_candidates.iter_mut().map(|(_, candidate)| candidate).collect::<Vec<_>>();

        // Using the decision tree, now build up the blocks for each arm, and then
        // join them at the end to the next block after the match, i.e. the `ending
        // block`.
        let ending_block =
            self.lower_match_arms(block, destination, subject.span(), span, &mut candidates);

        ending_block.unit()
    }

    fn create_match_candidates(
        &mut self,
        subject_place: &PlaceBuilder,
        arms: &'tcx AstNodes<MatchCase>,
    ) -> Vec<Candidates<'tcx>> {
        arms.iter()
            .map(|arm| {
                let arm = arm.ast_ref();
                let pat_id = self.get_pat_id_of_node(arm.pat.id());
                let candidate = Candidate::new(arm.span, pat_id, subject_place, arm.has_if_pat());
                (arm, candidate)
            })
            .collect()
    }

    fn lower_match_arms(
        &mut self,
        block: BasicBlock,
        destination: Place,
        subject_span: Span,
        span: Span,
        arm_candidates: &mut [&mut Candidate],
    ) -> BasicBlock {
        // This is the basic block that is derived for using when the
        // matching fails on the pattern, and that it should jump to
        // in the `otherwise` situation.
        let mut otherwise = None;

        self.match_candidates(span, block, &mut otherwise, arm_candidates);

        // We need to terminate the otherwise block with an `unreachable` since
        // this branch should never be reached since the `match` is exhaustive.
        if let Some(otherwise_block) = otherwise {
            self.control_flow_graph.terminate(
                otherwise_block,
                subject_span,
                TerminatorKind::Unreachable,
            );
        }

        todo!()
    }

    /// This is the main **entry point** of the match-lowering algorithm.
    fn match_candidates(
        &mut self,
        span: Span,
        block: BasicBlock,
        otherwise: &mut Option<BasicBlock>,
        candidates: &mut [&mut Candidate],
    ) {
        // Start by simplifying the candidates, i.e. splitting them into sub-candidates
        // so that they can be dealt with in a much easier way. If any of the
        // candidates we're split in the simplification process, we need to
        // later re-add them to the `candidates` list so that when they are
        // actually generated, they can be generated for only simple candidates,
        // and that all of them are dealt with.
        let mut split_or_candidate = false;

        for candidate in &mut *candidates {
            split_or_candidate |= self.simplify_candidate(candidate);
        }

        ensure_sufficient_stack(|| {
            if split_or_candidate {
                let mut new_candidates = Vec::new();

                // Iterate over all of the candidates and essentially flatten the
                // candidate list...
                for candidate in candidates {
                    candidate.visit_leaves(|leaf| new_candidates.push(leaf));
                }

                self.match_simplified_candidates(span, block, otherwise, &mut new_candidates)
            } else {
                self.match_simplified_candidates(span, block, otherwise, candidates)
            }
        });
    }

    fn match_simplified_candidates(
        &mut self,
        span: Span,
        start_block: BasicBlock,
        otherwise_block: &mut Option<BasicBlock>,
        candidates: &mut [&mut Candidate],
    ) {
        // since the candidates are sorted by priority, check candidates in order
        // whether they have satisfied all of the patterns that are specified.
        let all_matches = candidates.iter().take_while(|c| c.pairs.is_empty()).count();

        // Deal with matched/un-matched candidates separately.
        let (matched_candidates, unmatched_candidates) = candidates.split_at_mut(all_matches);

        let block = if !matched_candidates.is_empty() {
            let otherwise_block = self.select_match_candidates(matched_candidates, start_block);

            if let Some(otherwise) = otherwise_block {
                otherwise
            } else {
                // All other candidates after this point are unreachable, so we can
                // just remove
                if unmatched_candidates.is_empty() {
                    return;
                }

                self.control_flow_graph.start_new_block()
            }
        } else {
            start_block
        };

        // If there are no unmatched candidates, then we don't need
        // to create tests for any of the un-matched candidates.
        if unmatched_candidates.is_empty() {
            if let Some(otherwise) = *otherwise_block {
                self.control_flow_graph.goto(block, otherwise, span);
            } else {
                *otherwise_block = Some(block);
            }

            return;
        }

        // Otherwise, we need to create tests for all of the unmatched candidates.
        self.test_candidates_with_or(span, unmatched_candidates, block, otherwise_block)
    }

    /// Link matching candidates together, so that they are essentially chained.
    /// For example, if we have the following patterns:
    /// ```ignore
    /// 
    /// Some(x) if x > 10 => { ... }  Candidate #1
    /// Some(x) => { ... }            Candidate #2  
    /// Some(x) if x < 7 => { ... }   Candidate #3
    /// ```
    ///
    /// First, we bind the starting block to the `pre_binding_block` of the #1,
    /// then `otherwise_block` of #1 is linked to the `pre_binding_block` of #2,
    /// similarly for #2 and #3. The `otherwise_block` of #3 is then linked to
    /// a block that is marked as *Unreachable*. N.B. In practise, pattern #3 is
    /// never reached, since #2 is irrefutable in this case.
    fn select_match_candidates(
        &mut self,
        candidates: &mut [&mut Candidate],
        start_block: BasicBlock,
    ) -> Option<BasicBlock> {
        debug_assert!(
            !candidates.is_empty(),
            "select_match_candidates: candidates must not be empty"
        );
        debug_assert!(
            candidates.iter().all(|c| c.pairs.is_empty()),
            "select_match_candidates: candidates must be matched"
        );

        // Find the first index of a candidate that doesn't have a guard.
        let first_guard =
            candidates.iter().position(|c| !c.has_guard).unwrap_or(candidates.len() - 1);

        // Split the candidates between this point
        let (reachable_candidates, unreachable_candidates) = candidates.split_at_mut(first_guard);

        let mut next_pre_binding_block = start_block;

        for candidate in reachable_candidates.iter_mut() {
            candidate.pre_binding_block = Some(next_pre_binding_block);

            // Create a new block for the next candidate to jump to, which
            // becomes that pre-binding block for the next candidate.
            next_pre_binding_block = self.control_flow_graph.start_new_block();
            candidate.otherwise_block = Some(next_pre_binding_block);
        }

        // Add blocks for all of the unreachable candidates...
        for candidate in unreachable_candidates {
            candidate.pre_binding_block = Some(self.control_flow_graph.start_new_block());
        }

        reachable_candidates.last_mut().unwrap().otherwise_block
    }

    /// Test the remaining candidates whether there are only `or` pattern left,
    /// if not then we start building tests for candidates.
    fn test_candidates_with_or(
        &mut self,
        span: Span,
        candidates: &mut [&mut Candidate],
        block: BasicBlock,
        otherwise_block: &mut Option<BasicBlock>,
    ) {
        // we get the first candidate, and test if it is an or pattern, if
        // it is, then all proceeding candidates are or patterns, since we
        // sorted them by priority (all or-patterns go to the end)
        let (first, remaining) = candidates.split_first_mut().unwrap();

        let is_or_pat = self.tcx.pat_store.map_fast(first.pairs[0].pat, |pat| pat.is_or());

        // If this is the case, it means that we have no or-patterns
        // here... since we sorted them
        if !is_or_pat {
            self.test_candidates(span, candidates, block, otherwise_block);
            return;
        }

        let pairs = mem::take(&mut first.pairs);
        first.pre_binding_block = Some(block);

        let mut otherwise = None;

        for pair in pairs {
            let pats = self.tcx.pat_store.map_fast(pair.pat, |pat| {
                let Pat::Or(pats) = pat else {
                    unreachable!("`or` pattern expected after candidate sorting")
                };

                pats.clone()
            });

            first.visit_leaves(|leaf| {
                self.test_or_pat(leaf, &mut otherwise, &pats);
            });
        }

        // we then create a remained block to start off all the remaining candidates
        let remainder_start =
            otherwise.unwrap_or_else(|| self.control_flow_graph.start_new_block());

        self.match_candidates(span, remainder_start, otherwise_block, remaining);
    }
}
