//! Module that contains all of the logic with dealing with `match` blocks.
//! Lowering `match` blocks is probably the most complex part of lowering, since
//! we have to create essentially a *jump* table each case that is specified in
//! the `match` arms, which might also have `if` guards, `or` patterns, etc.
mod candidate;
mod const_range;
mod declarations;
mod optimise;
mod test;

use std::mem;

use hash_ast::ast::{self, AstNodeId};
use hash_ir::{
    ir::{self, BasicBlock, LogicalBinOp, Place, RValue, TerminatorKind},
    ty::{Mutability, RefKind},
};
use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::{Context, ScopeKind},
    control::{IfPat, MatchCasesId},
    node::NodesId,
    pats::{Pat, PatId},
    terms::{Term, TermId},
};
use hash_utils::{itertools::Itertools, stack::ensure_sufficient_stack};

use self::{
    candidate::{traverse_candidate, Binding, Candidate, Candidates},
    test::TestKind,
};
use super::{
    place::PlaceBuilder, ty::FnCallTermKind, unpack, BlockAnd, BlockAndExtend, BodyBuilder,
};

impl<'tcx> BodyBuilder<'tcx> {
    /// This is the entry point of matching an expression. Firstly, we deal with
    /// the subject of the match, and then we build a decision tree of all
    /// of the arms that have been specified, then we create all of the
    /// blocks that are required to represent the decision tree. After the
    /// decision tree has been built, we then build the blocks
    /// that are required to represent the actual match arms.
    pub(crate) fn lower_match_term(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        origin: AstNodeId,
        subject: TermId,
        arms: MatchCasesId,
        match_origin: ast::MatchOrigin,
    ) -> BlockAnd<()> {
        // @@Hack: if the match-origin is an `if`-chain, then we don't bother
        // lowering the place since we always know that the branches are
        // always matching, and it's only guards that are being tested. Therefore,
        // we use the `subject_place` as the `return_place` in this instance.
        let subject_place = if matches!(match_origin, ast::MatchOrigin::If) {
            PlaceBuilder::from(ir::RETURN_PLACE)
        } else {
            unpack!(block = self.as_place_builder(block, subject, Mutability::Mutable))
        };

        let subject_span = self.span_of_term(subject);

        // Make the decision tree here...
        let mut arm_candidates = self.create_match_candidates(&subject_place, arms);

        let mut candidates =
            arm_candidates.iter_mut().map(|(_, candidate)| candidate).collect::<Vec<_>>();

        // Using the decision tree, now build up the blocks for each arm, and then
        // join them at the end to the next block after the match, i.e. the `ending
        // block`.
        self.lower_match_tree(block, subject_span, origin, &mut candidates);
        self.lower_match_arms(destination, subject_span, arm_candidates)
    }

    fn create_match_candidates(
        &mut self,
        subject_place: &PlaceBuilder,
        arms: MatchCasesId,
    ) -> Vec<Candidates<'tcx>> {
        arms.elements()
            .borrow()
            .iter()
            .copied()
            .map(|arm| {
                let span = self.span_of_pat(arm.bind_pat);
                let has_guard = arm.bind_pat.borrow().is_if();

                let candidate = Candidate::new(span, arm.bind_pat, subject_place, has_guard);
                (*arm, candidate)
            })
            .collect()
    }

    /// This function is used to create a `then-else` block sequence for a
    /// specified expression. This is used to deal with `if-guards`, and to
    /// also capture behaviour of short-circuiting logic operations, such as
    /// `&&` and `||`.
    pub(crate) fn then_else_break(
        &mut self,
        mut block: BasicBlock,
        else_block: BasicBlock,
        expr: TermId,
    ) -> BlockAnd<()> {
        let span = self.span_of_term(expr);

        // If this is a `&&`, we can create a `then-else` block sequence
        // that respects the short-circuiting behaviour of `&&`.
        if let Term::FnCall(ref fn_call) = *expr.value() {
            if let FnCallTermKind::LogicalBinOp(LogicalBinOp::And, lhs, rhs) =
                self.classify_fn_call_term(fn_call)
            {
                let lhs_then_block = unpack!(self.then_else_break(block, else_block, lhs));
                let rhs_then_block = unpack!(self.then_else_break(lhs_then_block, else_block, rhs));
                return rhs_then_block.unit();
            }
        }

        let place = unpack!(block = self.as_place(block, expr, Mutability::Mutable));
        let then_block = self.control_flow_graph.start_new_block();

        let terminator = TerminatorKind::make_if(place.into(), then_block, else_block);
        self.control_flow_graph.terminate(block, span, terminator);

        then_block.unit()
    }

    /// Create a decision tree for the match expression using all of the created
    /// [Candidate]s. The tree starts from the specified `block`, and this
    /// will recursively create a decision tree using `match_candidates`. At
    /// the end, we link up all of the [Candidate]s with the
    /// `next_pre_binding_block` so that it can act as a "fallthrough" block.
    ///
    /// This function will modify the `candidates` to store all of the creates
    /// bindings for the specified pattern.
    fn lower_match_tree(
        &mut self,
        block: BasicBlock,
        subject_origin: AstNodeId,
        origin: AstNodeId,
        candidates: &mut [&mut Candidate],
    ) {
        // This is the basic block that is derived for using when the
        // matching fails on the pattern, and that it should jump to
        // in the `otherwise` situation.
        let mut otherwise = None;

        self.match_candidates(origin, block, &mut otherwise, candidates);

        // We need to terminate the otherwise block with an `unreachable` since
        // this branch should never be reached since the `match` is exhaustive.
        if let Some(otherwise_block) = otherwise {
            self.control_flow_graph.terminate(
                otherwise_block,
                subject_origin,
                TerminatorKind::Unreachable,
            );
        }

        // Link each leaf candidate to the `pre_binding_block` of the next candidate.
        let mut previous_candidate: Option<&mut Candidate> = None;
        for candidate in candidates {
            candidate.visit_leaves(|leaf| {
                if let Some(ref mut prev) = previous_candidate {
                    prev.next_candidate_pre_bind_block = leaf.pre_binding_block;
                }

                previous_candidate = Some(leaf);
            });
        }
    }

    /// This function will lower the bindings, guards and the bodies of the arms
    /// in the `match` expression. This is done after the decision tree is
    /// computed, so that we can link up  all of the appropriate decisions
    /// to their corresponding arms.
    fn lower_match_arms(
        &mut self,
        destination: Place,
        subject_origin: AstNodeId,
        arm_candidates: Vec<Candidates<'tcx>>,
    ) -> BlockAnd<()> {
        // Lower all of the arms...
        let mut lowered_arms_edges: Vec<_> = Vec::with_capacity(arm_candidates.len());

        for (arm, candidate) in arm_candidates {
            // Each match-case creates its own scope, so we need to enter it here...
            Context::enter_resolved_scope_mut(self, ScopeKind::Stack(arm.stack_id), |this| {
                this.declare_bindings(arm.bind_pat);
                let arm_block = this.bind_pat(subject_origin, arm.bind_pat, candidate);
                lowered_arms_edges.push(this.term_into_dest(destination, arm_block, arm.value));
            })
        }

        // After the execution of the match, all branches end up here...
        let end_block = self.control_flow_graph.start_new_block();

        // Link up all of the arms with the ending block
        for arm_edge in lowered_arms_edges {
            // get the span of the last statement
            let span = self.control_flow_graph.basic_blocks[arm_edge.0]
                .statements
                .last()
                .map(|stmt| stmt.origin)
                .unwrap_or(subject_origin);

            let arm_block_edge = unpack!(arm_edge);

            // In the event that this block has already been terminated
            // due to a `break` or `continue` or `return` control flow
            // statement, then we don't terminate this block again.
            if !self.control_flow_graph.is_terminated(arm_block_edge) {
                self.control_flow_graph.goto(arm_block_edge, end_block, span);
            }
        }

        end_block.unit()
    }

    /// This is the main **entry point** of the match-lowering algorithm.
    fn match_candidates(
        &mut self,
        origin: AstNodeId,
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

                self.match_simplified_candidates(origin, block, otherwise, &mut new_candidates)
            } else {
                self.match_simplified_candidates(origin, block, otherwise, candidates)
            }
        });
    }

    fn match_simplified_candidates(
        &mut self,
        origin: AstNodeId,
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
                self.control_flow_graph.goto(block, otherwise, origin);
            } else {
                *otherwise_block = Some(block);
            }

            return;
        }

        // Otherwise, we need to create tests for all of the unmatched candidates.
        self.test_candidates_with_or(origin, unmatched_candidates, block, otherwise_block)
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
        let (reachable_candidates, unreachable_candidates) =
            candidates.split_at_mut(first_guard + 1);

        let mut next_pre_binding_block = start_block;

        for candidate in reachable_candidates.iter_mut() {
            debug_assert!(candidate.otherwise_block.is_none());
            debug_assert!(candidate.pre_binding_block.is_none());

            candidate.pre_binding_block = Some(next_pre_binding_block);

            // Create a new block for the next candidate to jump to, which
            // becomes that pre-binding block for the next candidate.
            if candidate.has_guard {
                next_pre_binding_block = self.control_flow_graph.start_new_block();
                candidate.otherwise_block = Some(next_pre_binding_block);
            }
        }

        // Add blocks for all of the unreachable candidates...
        for candidate in unreachable_candidates {
            debug_assert!(candidate.pre_binding_block.is_none());

            candidate.pre_binding_block = Some(self.control_flow_graph.start_new_block());
        }

        reachable_candidates.last_mut().unwrap().otherwise_block
    }

    /// Test the remaining candidates whether there are only `or` pattern left,
    /// if not then we start building tests for candidates.
    fn test_candidates_with_or(
        &mut self,
        origin: AstNodeId,
        candidates: &mut [&mut Candidate],
        block: BasicBlock,
        otherwise_block: &mut Option<BasicBlock>,
    ) {
        // we get the first candidate, and test if it is an or pattern, if
        // it is, then all proceeding candidates are or patterns, since we
        // sorted them by priority (all or-patterns go to the end)
        let (first, remaining) = candidates.split_first_mut().unwrap();

        // If this is the case, it means that we have no or-patterns
        // here... since we sorted them
        if !first.pairs[0].pat.borrow().is_or() {
            self.test_candidates(origin, candidates, block, otherwise_block);
            return;
        }

        let pairs = mem::take(&mut first.pairs);
        first.pre_binding_block = Some(block);

        let mut otherwise = None;

        for pair in pairs {
            let or_span = self.span_of_pat(pair.pat);
            let Pat::Or(pats) = *pair.pat.value() else {
                unreachable!("`or` pattern expected after candidate sorting")
            };

            let pats = pats
                .alternatives
                .elements()
                .borrow()
                .iter()
                .map(|pat| pat.assert_pat())
                .collect_vec();

            first.visit_leaves(|leaf| {
                self.test_or_pat(leaf, &mut otherwise, &pair.place, &pats, or_span);
            });
        }

        // we then create a remained block to start off all the remaining candidates
        let remainder_start =
            otherwise.unwrap_or_else(|| self.control_flow_graph.start_new_block());

        self.match_candidates(origin, remainder_start, otherwise_block, remaining);
    }

    /// This is the point where we begin to "test" candidates since we have
    /// simplified all of the candidates as much as possible. We take the
    /// first candidate from the provided list, and take the first pattern
    /// within it's list that it must satisfy. Then we decide what kind of
    /// test to perform based on the type of the pattern.
    ///
    /// After we know what test is going to be performed on the candidate, we
    /// can cut down the number of candidates (from high to low priority)
    /// and check.
    ///
    /// There are situations where this does not apply, for example:
    /// ```ignore
    /// (x, y, z) := (true, true, true)
    ///
    /// match (x, y, z) {
    ///    (true ,     _, true ) => { ... } Candidate #1
    ///    (_    ,  true, _    ) if x == false => { ... } Candidate #2
    ///    (false, false, _    ) => { ... } Candidate #3
    ///    (true ,     _, false) => { ... } Candidate #4
    /// }
    /// ```
    ///
    /// When we test `x`, there are two overlapping sets:
    ///
    /// - If `x` is `true`, then we have candidates #1, #2, and #4
    /// - If `x` is `false`, then we have candidates #2, #3
    ///
    /// This would generate separate code-paths for these two cases. In some
    /// cases, this would produce exponential behaviour (and thus exponential
    /// amount of code). This might not actually show up in real scenarios,
    /// but a simple scenario which is realistic might be:
    /// ```ignore
    /// match x {
    ///    "a" if a => { ... }
    ///    "b" if b => { ... }
    ///    "c" if c => { ... }
    /// }
    /// ```
    ///
    /// Here, we use a [TestKind::Eq] since we need to perform an equality test
    /// between the string literal and `x`. Using the standard approach, we
    /// wouldn't generate two distinct sets of two values, since `"a"` might
    /// be matched later by some other branch, which would then lead to an
    /// exponential number of tests occurring.
    ///
    /// To avoid this, we try to ensure that the amount of generated tests is
    /// linear. We do this by doing a k-way test, which returns an additional
    /// "unmatched" set alongside the matches `k` set. When we encounter a
    /// candidate that would present in more than one of the sets, we put it
    /// and all candidates below it in an "unmatched" set. This ensures that
    /// these sets are disjoint, which means we don't need to perform more
    /// than k + 1 tests.
    ///
    /// Once a test is performed, we branch into the appropriate candidate set,
    /// and then recursively call `match_candidates`. These sub-matches are
    /// non-exhaustive (since we discarded the `otherwise` set) - so we
    /// continue with the "unmatched" set with `match_candidates` Using this
    /// approach, we essentially generate an `if-else-if` chain.
    fn test_candidates(
        &mut self,
        origin: AstNodeId,
        mut candidates: &mut [&mut Candidate],
        block: BasicBlock,
        otherwise: &mut Option<BasicBlock>,
    ) {
        // take the first pattern
        let pair = &candidates.first().unwrap().pairs[0];
        let mut test = self.test_match_pair(pair);
        let match_place = pair.place.clone();

        // For switch tests, we may want to add additional cases to the
        // test from the available candidates
        match test.kind {
            TestKind::Switch { options: ref mut variants, .. } => {
                for candidate in candidates.iter() {
                    // If we couldn't add a particular candidate, then short-circuit
                    // since we won't be able to add any candidates after.
                    if !self.add_variants_to_switch(&match_place, candidate, variants) {
                        break;
                    }
                }
            }
            TestKind::SwitchInt { ref mut options, .. } => {
                for candidate in candidates.iter() {
                    // If we couldn't add a particular candidate, then short-circuit
                    // since we won't be able to add any candidates after.
                    if !self.add_cases_to_switch(&match_place, candidate, options) {
                        break;
                    }
                }
            }
            _ => {}
        };

        // Create a collection that represent `target_candidates` which
        // will be used to store the candidates that still apply after
        // a test.
        let mut target_table: Vec<Vec<&mut Candidate>> = Vec::new();

        // we know the exact size of the targets, so we can pre-allocate
        // the size we need
        target_table.resize_with(test.targets(), Default::default);

        let candidate_count = candidates.len();

        // Sort the candidates into each appropriate vector within the `target_map`.
        // If we encounter a candidate that the test does not apply to, then we
        // stop sorting since there will be no further candidates that the test applies
        // to.
        while let Some(candidate) = candidates.first_mut() {
            let Some(index) = self.sort_candidate(&match_place, &test, candidate) else {
                break;
            };

            let (candidate, rest) = candidates.split_first_mut().unwrap();
            target_table[index].push(candidate);
            candidates = rest;
        }

        // We should have at-least removed the first candidate.
        debug_assert!(candidate_count > candidates.len());

        let make_target_blocks = move |this: &mut Self| -> Vec<BasicBlock> {
            // If none of the `target_table` entries match, then we use this
            // as the place to branch to. This is either the block where we
            // started matching the untested candidates in `match_candidates`,
            // or it's the `otherwise` block.
            let remainder_start = &mut None;
            let remainder_start =
                if candidates.is_empty() { &mut *otherwise } else { remainder_start };

            // For every outcome of the test, process the candidates that still
            // apply, collect a list of block where the control flow will branch if
            // one of the `target_table` entries sets is not exhaustive.
            let target_blocks: Vec<_> = target_table
                .into_iter()
                .map(|mut candidates| {
                    if !candidates.is_empty() {
                        let candidate_start = this.control_flow_graph.start_new_block();

                        this.match_candidates(
                            origin,
                            candidate_start,
                            remainder_start,
                            &mut candidates,
                        );
                        candidate_start
                    } else {
                        *remainder_start
                            .get_or_insert_with(|| this.control_flow_graph.start_new_block())
                    }
                })
                .collect();

            if !candidates.is_empty() {
                let remainder_start =
                    remainder_start.unwrap_or_else(|| this.control_flow_graph.start_new_block());
                this.match_candidates(origin, remainder_start, otherwise, candidates);
            };

            target_blocks
        };

        self.perform_test(origin, block, &match_place, &test, make_target_blocks);
    }

    /// This function is responsible for putting all of the declared bindings
    /// into scope.
    fn bind_pat(&mut self, origin: AstNodeId, pat: PatId, candidate: Candidate) -> BasicBlock {
        let guard = match *pat.value() {
            Pat::If(IfPat { condition, .. }) => Some(condition),
            _ => None,
        };

        if candidate.sub_candidates.is_empty() {
            // We don't need generate another `BasicBlock` when we only have
            // this candidate.
            self.bind_and_guard_matched_candidate(candidate, guard, &[], origin)
        } else {
            let target_block = self.control_flow_graph.start_new_block();

            traverse_candidate(
                candidate,
                &mut Vec::new(),
                &mut |leaf, parent_bindings| {
                    let binding_end =
                        self.bind_and_guard_matched_candidate(leaf, guard, parent_bindings, origin);
                    self.control_flow_graph.goto(binding_end, target_block, origin);
                },
                |inner, parent_bindings| {
                    parent_bindings.push(inner.bindings);
                    inner.sub_candidates.into_iter()
                },
                |parent_bindings| {
                    parent_bindings.pop();
                },
            );

            target_block
        }
    }

    /// Function that initialised each of the bindings from the candidate by
    /// performing an a ref/copy as appropriate. Additionally, this will
    /// test if there is a guard, and it will generate the guard basic
    /// blocks, and then it will move onto the arm of the match.
    ///
    /// @@Todo: support specifically generating `if-guards` for sub-patterns.
    ///
    /// @@Todo: we need to specifically deny any `if-guards` from **mutating**
    /// the bindings, so possibly wrap them in a ref?
    fn bind_and_guard_matched_candidate(
        &mut self,
        candidate: Candidate,
        guard: Option<TermId>,
        parent_bindings: &[Vec<Binding>],
        origin: AstNodeId,
    ) -> BasicBlock {
        let block = candidate.pre_binding_block.unwrap();

        // If this has a guard, then we need to create more blocks for the event
        // that the guard does not succeed and we backtrack to the next patterns.
        if candidate.has_guard && let Some(guard) = guard {
            let bindings = parent_bindings
                .iter()
                .flatten()
                .chain(&candidate.bindings);

            // bind everything necessary for the guard.
            self.bind_matched_candidate_for_guard(block, bindings);

            let otherwise_block = candidate.otherwise_block.unwrap_or_else(|| {
                let unreachable = self.control_flow_graph.start_new_block();
                self.control_flow_graph.terminate(unreachable, origin, TerminatorKind::Unreachable);
                unreachable
            });

            // deal with the if-guard
            let post_guard_block = unpack!(self.then_else_break(block, otherwise_block, guard));
            self.bind_matched_candidate_for_arm_body(
                post_guard_block, parent_bindings.iter().flatten().chain(&candidate.bindings));

            post_guard_block
        } else {
            self.bind_matched_candidate_for_arm_body(block, parent_bindings.iter().flatten().chain(&candidate.bindings));
            block
        }
    }

    /// Assign all of the bindings that are in scope for the `if-guard`. For
    /// now, we will automatically wrap any binding that is made by a
    /// reference (this might change in the future when this is determined
    /// more semantically).
    fn bind_matched_candidate_for_guard<'b>(
        &mut self,
        block: BasicBlock,
        bindings: impl IntoIterator<Item = &'b Binding>,
    ) where
        'tcx: 'b,
    {
        // assign each of the bindings, since this the guard expression there
        // should be only references to values that the if-guard references in order
        // to avoid problems of mutation in the if-guard, and then affecting the
        // soundness of later match checks.
        for binding in bindings {
            let value_place = Place::from_local(self.lookup_local(binding.name).unwrap());

            // @@Todo: we might have to do some special rules for the `by-ref` case
            //         when we start to think about reference rules more concretely.
            // let rvalue = RValue::Ref(binding.mutability, binding.source, RefKind::Raw);
            self.control_flow_graph.push_assign(
                block,
                value_place,
                binding.source.into(),
                binding.origin,
            );
        }
    }

    fn bind_matched_candidate_for_arm_body<'b>(
        &mut self,
        block: BasicBlock,
        bindings: impl IntoIterator<Item = &'b Binding>,
    ) where
        'tcx: 'b,
    {
        for binding in bindings {
            let rvalue = match binding.mode {
                candidate::BindingMode::ByValue => binding.source.into(),
                candidate::BindingMode::ByRef => {
                    RValue::Ref(binding.mutability, binding.source, RefKind::Raw)
                }
            };

            // Now resolve where the binding place from, and then push
            // an assign onto the binding source.
            let value_place = Place::from_local(self.lookup_local(binding.name).unwrap());

            self.control_flow_graph.push_assign(block, value_place, rvalue, binding.origin);
        }
    }
}
