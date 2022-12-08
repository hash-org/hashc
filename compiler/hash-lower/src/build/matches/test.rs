//! Definitions for [Test]s that is used to represent what kind
//! of test needs to be performed on a particular set of candidates
//! when deciding where to jump to within the decision tree.

use std::cmp::Ordering;

use fixedbitset::FixedBitSet;
use hash_ast::ast::RangeEnd;
use hash_ir::{
    ir::{
        BasicBlock, BinOp, Const, PlaceProjection, RValue, RValueId, SwitchTargets, TerminatorKind,
    },
    ty::{AdtData, AdtId, IrTy, IrTyId},
    IrStorage,
};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    constant::{IntConstant, CONSTANT_MAP},
    location::Span,
};
use hash_types::{
    fmt::PrepareForFormatting,
    pats::{AccessPat, ConstructorPat, IfPat, Pat, PatArgsId, PatId, RangePat},
};
use hash_utils::store::{CloneStore, SequenceStore, Store};
use indexmap::IndexMap;

use super::{
    candidate::{self, Candidate, MatchPair},
    utils::ConstRange,
};
use crate::build::{
    place::PlaceBuilder,
    ty::{constify_lit_term, evaluate_int_lit_term},
    Builder,
};

#[derive(PartialEq, Eq, Debug)]
pub(super) enum TestKind {
    /// Test what value an `enum` variant is.
    Switch {
        /// The id of the ADT that the switch is being performed on.
        adt: AdtId,

        /// All of the allowed variants for this particular switch.
        options: FixedBitSet,
    },

    SwitchInt {
        /// The type that is being tested, it is either a `integral`, `char` or
        /// `bool`.
        ty: IrTyId,

        /// The constants that are being tested, they are all integers in an
        /// ordered map.
        options: IndexMap<Const, u128>,
    },

    /// Equality test, for values that cannot be tested using a switch test.
    Eq {
        /// The type of the equality test, whether it is a `f32`, `f64` or `str`
        /// or some reference type.
        ty: IrTyId,

        /// The constant that is being compared to.
        value: Const,
    },

    /// Test whether the value falls within this particular range of values.
    Range { range: ConstRange },

    /// Test the length of the a slice/array pattern. This has an associated
    /// length and an operator, which is strictly an comparison operator of
    /// some kind, i.e. `==` `>=`, `>`, etc.
    Len {
        /// The length we are testing for.
        len: usize,

        /// What operator to use when testing for this value
        op: BinOp,
    },
}

/// A [Test] represents a test that will be carried out on a
/// a particular [Candidate].
pub(super) struct Test {
    /// The kind of test that is being performed on the candidate
    pub kind: TestKind,

    /// The span of where the test occurs, in order to provide richer
    /// information to basic block terminations when actually *performing*
    /// the test
    pub span: Span,
}

impl Test {
    /// Return the total amount of targets that a particular
    /// [Test] yields.
    pub(super) fn targets(&self, storage: &IrStorage) -> usize {
        match self.kind {
            TestKind::Switch { adt, .. } => {
                // The switch will not (necessarily) generate branches
                // for all of the variants, so we have a target for each
                // variant, and an additional target for the `otherwise` case.
                storage.adt_store().map_fast(adt, |adt| adt.variants.len() + 1)
            }
            TestKind::SwitchInt { ty, ref options } => {
                storage.ty_store().map_fast(ty, |ty| {
                    // The boolean branch is always 2...
                    if let IrTy::Bool = ty {
                        2
                    } else {
                        // @@FixMe: this isn't always true since the number of options
                        // might be exhaustive of the type, and so we don't necessarily
                        // have to add the `otherwise` branch. However, this is a case that
                        // doesn't often occur, so we can just ignore it for now.
                        options.len() + 1
                    }
                })
            }

            // These variants are always `true` or otherwise...
            TestKind::Eq { .. } | TestKind::Range { .. } | TestKind::Len { .. } => 2,
        }
    }
}

impl<'tcx> Builder<'tcx> {
    pub(super) fn test_or_pat(
        &mut self,
        candidate: &mut Candidate,
        otherwise: &mut Option<BasicBlock>,
        place_builder: &PlaceBuilder,
        pats: &[PatId],
        or_span: Span,
    ) {
        let mut or_candidates: Vec<_> = pats
            .iter()
            .map(|pat| {
                let span = self.span_of_pat(*pat);

                self.tcx.pat_store.map_fast(*pat, |pattern| {
                    Candidate::new(
                        span,
                        *pat,
                        place_builder,
                        pattern.is_if() || candidate.has_guard,
                    )
                })
            })
            .collect();

        let mut or_candidates_ref: Vec<_> = or_candidates.iter_mut().collect();

        let otherwise = if candidate.otherwise_block.is_some() {
            &mut candidate.otherwise_block
        } else {
            otherwise
        };

        // Perform the algorithm on these or-pats, and then attempt
        // to simplify anthing trivial, and assume the starting block
        // is the pre-binding block of the overall candidate.
        self.match_candidates(
            or_span,
            candidate.pre_binding_block.unwrap(),
            otherwise,
            &mut or_candidates_ref,
        );
        self.merge_sub_candidates(candidate, or_span);
    }

    /// Create a [Test] from a [MatchPair]. If this function is called
    /// on a un-simplified pattern, then this breaks an invariant and the
    /// function will panic.
    pub(super) fn test_match_pair(&mut self, pair: &MatchPair) -> Test {
        self.tcx.pat_store.map_fast(pair.pat, |pat| {
            // get the location of the pattern
            let span = self.span_of_pat(pair.pat);

            match pat {
                Pat::Access(AccessPat { subject, .. }) => {
                    let ty = self.ty_of_pat(*subject);
                    let (variant_count, adt) =
                        self.map_on_adt(ty, |adt, id| (adt.variants.len(), id));

                    Test {
                        kind: TestKind::Switch {
                            adt,
                            options: FixedBitSet::with_capacity(variant_count),
                        },
                        span,
                    }
                }
                Pat::Lit(term) => {
                    let ty = self.ty_of_pat(pair.pat);
                    let value = constify_lit_term(*term, self.tcx);

                    // If it is not an integral constant, we use an `Eq` test. This will
                    // happen when the constant is either a float or a string.
                    if value.is_integral() {
                        Test { kind: TestKind::SwitchInt { ty, options: Default::default() }, span }
                    } else {
                        Test { kind: TestKind::Eq { ty, value }, span }
                    }
                }
                Pat::Range(range_pat) => Test {
                    kind: TestKind::Range { range: ConstRange::from_range(range_pat, self.tcx) },
                    span,
                },
                Pat::List(list_pat) => {
                    let (prefix, suffix, rest) = list_pat.into_parts(self.tcx);

                    let len = prefix.len() + suffix.len();
                    let op = if rest.is_some() { BinOp::GtEq } else { BinOp::Eq };

                    Test { kind: TestKind::Len { len, op }, span }
                }
                Pat::If(IfPat { pat, .. }) => {
                    self.test_match_pair(&MatchPair { pat: pair.pat, place: pair.place.clone() })
                }
                Pat::Or(_) => panic_on_span!(
                    span.into_location(self.source_id),
                    self.source_map,
                    "or patterns should be handled by `test_or_pat`"
                ),
                Pat::Const(_)
                | Pat::Constructor(_)
                | Pat::Wild
                | Pat::Spread(_)
                | Pat::Tuple(_)
                | Pat::Mod(_)
                | Pat::Binding(_) => {
                    panic_on_span!(
                        span.into_location(self.source_id),
                        self.source_map,
                        "attempt to test simplify-able pattern, `{}`",
                        pair.pat.for_formatting(self.tcx)
                    )
                }
            }
        })
    }

    /// The `Test` is a specification of a specific test that we are performing
    /// with a `test_place` and a candidate. This function is responsible
    /// for computing the **status** of the candidate after the test is
    /// performed. The status is represented as the index of where the
    /// candidate should be placed in the `candidates` vector. Additionally,
    /// the [Candidate] place may be modified to update the `pairs` place.
    pub(super) fn sort_candidate(
        &mut self,
        match_place: &PlaceBuilder,
        test: &Test,
        candidate: &mut Candidate,
    ) -> Option<usize> {
        // firstly, find the `test_place` within the candidate, there can only
        // be one matching place.
        let (pair_index, pair) = {
            candidate
                .pairs
                .iter()
                .enumerate()
                .find(|(_, pair)| pair.place == *match_place)
                .map(|(index, item)| (index, item.clone()))?
        };

        self.tcx.pat_store.map_fast(pair.pat, |pat| match (&test.kind, pat) {
            (
                TestKind::Switch { adt, options },
                Pat::Constructor(ConstructorPat { subject, args }),
            ) => {
                // If we are performing a variant switch, then this informs
                // variant patterns, bu nothing else.
                let test_adt = self.convert_term_into_ir_ty(*subject);

                let variant_index = self.map_on_adt(test_adt, |adt, id| {
                    // If this is a struct, then we don't do anything
                    // since we're expecting an enum. Although, this case shouldn't happen?
                    if adt.flags.is_struct() {
                        return None;
                    }

                    Some(self.lower_enum_variant_ty(adt, *subject))
                })?;

                self.candidate_after_variant_switch(
                    pair_index,
                    *adt,
                    variant_index,
                    *args,
                    candidate,
                );

                Some(variant_index)
            }

            (TestKind::Switch { .. }, _) => None,

            // When we are performing a switch over integers, then this informs integer
            // equality, but nothing else, @@Improve: we could use the Pat::Range to rule
            // some things out.
            (TestKind::SwitchInt { ty, ref options }, Pat::Lit(lit)) => {
                // We can't really do anything here since we can't compare them with
                // the switch.
                if !self.storage.ty_store().map_fast(*ty, |ty| ty.is_integral()) {
                    return None;
                }

                // @@Todo: when we switch to new patterns, we can look this up without
                // the additional evaluation. However, we might need to modify the `Eq`
                // on `ir::Const` to actually check if integer values are equal.
                let (value, _) = evaluate_int_lit_term(*lit, self.tcx);
                let index = options.get_index_of(&value).unwrap();

                // remove the candidate from the pairs
                candidate.pairs.remove(pair_index);
                Some(index)
            }
            (TestKind::SwitchInt { ty, ref options }, Pat::Range(range_pat)) => {
                let not_contained =
                    self.values_not_contained_in_range(range_pat, options).unwrap_or(false);

                // If no switch values are contained within this range, so that pattern can only
                // be matched if the test fails.
                not_contained.then(|| options.len())
            }
            (TestKind::SwitchInt { .. }, _) => None,

            (TestKind::Len { len: test_len, op: BinOp::Eq }, Pat::List(list_pat)) => {
                let (prefix, suffix, rest) = list_pat.into_parts(self.tcx);
                let pat_len = prefix.len() + suffix.len();
                let ty = self.ty_of_pat(pair.pat);

                match (pat_len.cmp(test_len), rest) {
                    (Ordering::Equal, None) => {
                        self.candidate_after_slice_test(
                            ty, pair_index, candidate, &prefix, rest, &suffix,
                        );

                        Some(0)
                    }

                    // `test_len` < `pat_len`. If `actual_len` = `test_len`,
                    // then `actual_len` < `pat_len` and we don't have
                    // enough elements.
                    (Ordering::Less, _) => Some(1),
                    // `actual_len` >= `test_len`, and if the `actual_len` > `test_len` we cannot
                    // advance.
                    (Ordering::Equal | Ordering::Greater, Some(_)) => None,
                    // the `test_len` is != `pat_len`, so if `actual_len` = `test_len`, then
                    // `actual_len` != `pat_len`.
                    (Ordering::Greater, None) => Some(1),
                }
            }
            (TestKind::Len { len: test_len, op: BinOp::GtEq }, Pat::List(list_pat)) => {
                let (prefix, suffix, rest) = list_pat.into_parts(self.tcx);
                let pat_len = prefix.len() + suffix.len();

                let ty = self.ty_of_pat(pair.pat);

                match (pat_len.cmp(test_len), rest) {
                    (Ordering::Equal, Some(_)) => {
                        // `actual_len` >= `test_len` && `test_len` == `pat_len`, so we can
                        // advance.
                        self.candidate_after_slice_test(
                            ty, pair_index, candidate, &prefix, rest, &suffix,
                        );

                        Some(0)
                    }
                    // `test_len` <= `pat_len`. If `actual_len` < `test_len`,
                    // then it is also < `pat_len`, so the test passing is
                    // necessary (but insufficient).
                    (Ordering::Less, _) | (Ordering::Equal, None) => Some(0),
                    // `test_len` > `pat_len`. If `actual_len` >= `test_len` > `pat_len`,
                    // then we know we won't have a match.
                    (Ordering::Greater, None) => Some(1),
                    // `test_len` < `pat_len`, and is therefore less
                    // strict. This can still go both ways.
                    (Ordering::Greater, Some(_)) => None,
                }
            }

            (TestKind::Range { range }, Pat::Range(range_pat)) => {
                let actual_range = ConstRange::from_range(range_pat, self.tcx);

                if actual_range == *range {
                    // If the ranges are equal, then we can remove the candidate from the
                    // pairs.
                    candidate.pairs.remove(pair_index);
                    return Some(0);
                }

                // Check if the two ranged overlap, and if they don't then the pattern
                // can only be matched if this test fails
                if !range.overlaps(&actual_range)? {
                    Some(1)
                } else {
                    None
                }
            }
            (TestKind::Range { ref range }, Pat::Lit(lit_pat)) => {
                let (value, _) = evaluate_int_lit_term(*lit_pat, self.tcx);

                // If the `value` is not contained in the testing range, so the `value` can be
                // matched only if the test fails.
                if let Some(false) = range.contains(value) {
                    Some(1)
                } else {
                    None
                }
            }
            (TestKind::Range { range }, _) => None,
            (TestKind::Eq { .. } | TestKind::Len { .. }, _) => {
                // If we encounter here an or-pattern, then we need to return
                // from here because we will panic if we continue down this
                // branch, since the `test()` only expects fully simplified
                // patterns.
                if let Pat::Or(_) = pat {
                    return None;
                }

                // We make a test for the pattern to compare with the given test
                // to see if it is the same, if so we can match... @@Improve: we possibly avoid
                // this?
                let pat_test = self.test_match_pair(&pair);

                if pat_test.kind == test.kind {
                    // remove the candidate from the pairs
                    candidate.pairs.remove(pair_index);
                    Some(0)
                } else {
                    None
                }
            }
        })
    }

    /// This function is responsible for adjusting the [Candidate] after a
    /// slice test has been checked. This means that we remove the given
    /// `pair_index` from the candidate, and then adjust all of the prefix
    /// and the suffix places to be the correct places.
    fn candidate_after_slice_test(
        &mut self,
        ty: IrTyId,
        pair_index: usize,
        candidate: &mut Candidate,
        prefix: &[PatId],
        rest: Option<PatId>,
        suffix: &[PatId],
    ) {
        let removed_place = candidate.pairs.remove(pair_index).place;

        self.adjust_list_pat_candidates(
            ty,
            &mut candidate.pairs,
            &removed_place,
            prefix,
            rest,
            suffix,
        );
    }

    fn candidate_after_variant_switch(
        &mut self,
        pair_index: usize,
        adt: AdtId,
        variant_index: usize,
        sub_patterns: PatArgsId,
        candidate: &mut Candidate,
    ) {
        let pair = candidate.pairs.remove(pair_index);

        // we need to compute the subsequent match pairs after the downcastr
        // and add them to the candidate.
        let downcast_place = pair.place.downcast(variant_index);

        let consequent_pairs: Vec<_> = self.storage.adt_store().map_fast(adt, |adt| {
            let variant = &adt.variants[variant_index];

            self.tcx.pat_args_store.map_as_param_list_fast(sub_patterns, |pats| {
                pats.positional()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        let field_index = match arg.name {
                            Some(name) => variant.field_idx(name).unwrap(),
                            _ => index,
                        };

                        let place =
                            downcast_place.clone_project(PlaceProjection::Field(field_index));
                        MatchPair { place, pat: arg.pat }
                    })
                    .collect()
            })
        });

        candidate.pairs.extend(consequent_pairs);
    }

    /// This function is responsible for generating the code for the specified
    /// [Test].
    pub(super) fn perform_test(
        &mut self,
        span: Span,
        block: BasicBlock,
        place_builder: &PlaceBuilder,
        test: &Test,
        make_target_blocks: impl FnOnce(&mut Self) -> Vec<BasicBlock>,
    ) {
        // Build the place from the provided place builder
        let place = place_builder.clone().into_place();

        match test.kind {
            TestKind::Switch { adt, options: ref variants } => {
                let target_blocks = make_target_blocks(self);
                let (variant_count, discriminant_ty) = self
                    .storage
                    .adt_store()
                    .map_fast(adt, |adt| (adt.variants.len(), adt.discriminant_ty()));

                // Assert that the number of variants is the same as the number of
                // target blocks.
                debug_assert_eq!(variant_count + 1, target_blocks.len());

                let otherwise_block = target_blocks.last().copied();

                // Here we want to create a switch statement that will match on all of the
                // specified discriminants of the ADT.
                let discriminant_ty = self.storage.ty_store().create(discriminant_ty.into());
                let targets = SwitchTargets::new(
                    self.storage.adt_store().map_fast(adt, |adt| {
                        // Map over all of the discriminants of the ADT, and filter out those that
                        // are not in the `options` set.
                        adt.discriminants().filter_map(|(var_idx, discriminant)| {
                            let idx = var_idx.index();
                            if variants.contains(idx) {
                                Some((discriminant, target_blocks[idx]))
                            } else {
                                None
                            }
                        })
                    }),
                    discriminant_ty,
                    otherwise_block,
                );

                // Then we push an assignment to a the passed in `place` so that we
                // can compare the discriminant to the specified value within the
                // switch statement.
                let discriminant_tmp = self.temp_place(discriminant_ty);
                let value = self.storage.push_rvalue(RValue::Discriminant(place));
                self.control_flow_graph.push_assign(block, discriminant_tmp, value, span);

                // then terminate this block with the `switch` terminator
                self.control_flow_graph.terminate(
                    block,
                    span,
                    TerminatorKind::Switch { value, targets },
                );
            }
            TestKind::SwitchInt { ty, ref options } => {
                let target_blocks = make_target_blocks(self);

                let terminator_kind = if self.map_ty(ty, |ty| *ty == IrTy::Bool) {
                    debug_assert!(options.len() == 2);

                    let [first_block, second_block]= *target_blocks else {
                        panic!("expected two target blocks for boolean switch");
                    };

                    let (true_block, false_block) = match options[0] {
                        1 => (first_block, second_block),
                        0 => (second_block, first_block),
                        _ => panic!("expected boolean switch to have only two options"),
                    };

                    TerminatorKind::make_if(place, true_block, false_block, self.storage)
                } else {
                    debug_assert_eq!(options.len() + 1, target_blocks.len());
                    let otherwise_block = target_blocks.last().copied();

                    let targets = SwitchTargets::new(
                        options.values().copied().zip(target_blocks),
                        ty,
                        otherwise_block,
                    );

                    let value = self.storage.push_rvalue(RValue::Use(place));
                    TerminatorKind::Switch { value, targets }
                };

                self.control_flow_graph.terminate(block, span, terminator_kind);
            }
            TestKind::Eq { ty, value } => {
                let (is_str, is_scalar) =
                    self.map_ty(ty, |ty| (matches!(ty, IrTy::Str), ty.is_scalar()));

                // If this type is a string, we essentially have to make a call to
                // a string comparator function (which will be filled in later on
                // by the `codegen` pass).
                if is_str {
                    unimplemented!("string comparisons not yet implemented")
                }

                // If the type is a scalar, then we can just perform a binary
                // operation on the value, and then switch on the result
                if is_scalar {
                    let [success, fail] = *make_target_blocks(self) else {
                            panic!("expected two target blocks for `Eq` test");
                        };

                    let expected = self.storage.push_rvalue(RValue::Const(value));
                    let value = self.storage.push_rvalue(RValue::Use(place));

                    self.compare(block, success, fail, BinOp::Eq, expected, value, span);
                } else {
                    // @@Todo: here we essentially have to make a call to some alternative
                    //         equality mechanism since the [BinOp::EqEq] cannot handle
                    //         non-scalar types.
                    unimplemented!("non-scalar comparisons not yet implemented")
                }
            }
            TestKind::Range { range: ConstRange { lo, hi, end } } => {
                let lb_success = self.control_flow_graph.start_new_block();
                let target_blocks = make_target_blocks(self);

                let lo = self.storage.push_rvalue(RValue::Const(lo));
                let hi = self.storage.push_rvalue(RValue::Const(hi));
                let val = self.storage.push_rvalue(RValue::Use(place));

                let [success, fail] = *target_blocks else {
                    panic!("expected two target blocks for `Range` test");
                };

                // So here, we generate the control flow checks for the range comparison.
                // Firslty, we generate the check to see if the `value` is less
                // than or equal to the `lo` value. If so, the cfg progresses to
                // `lb_success` which means that is has passed the first check.
                // If not, then the cfg progresses to `fail` which means that the
                // value is not in the range, and we can stop there.
                //
                // If the check is successful, the cfg goes to check if the `value` is less than
                // (or equal to if inclusive range) and if so, then we go to the
                // `success` branch, otherwise we go to the `fail` branch as previously
                // specified. Here is a visual illustration of the control flow:
                //
                //```text
                //    +---------+
                //    |  block  |
                //    +----+----+
                //         |
                //         v
                //     +--+--+--+  (true)  +--------------+
                //     | >=lo?  |--------> | (< | <=) hi? |  ----+ (false)
                //     +---+----+          +------+-------+      |
                //         | (false)              | (true)       |
                //         v                      v              |
                //     +---+---+             +----+----+         |
                //     | fail  |             | success |         |
                //     +---+---+             +---------+         |
                //         ^                                     |
                //         |                                     |
                //         +-------------------------------------+
                //```

                // Generate the comparison for the lower bound
                self.compare(block, lb_success, fail, BinOp::LtEq, lo, val, span);

                let op = match end {
                    RangeEnd::Included => BinOp::LtEq,
                    RangeEnd::Excluded => BinOp::Lt,
                };

                self.compare(lb_success, success, fail, op, val, hi, span);
            }
            TestKind::Len { len, op } => {
                let target_blocks = make_target_blocks(self);

                let usize_ty = self.storage.ty_store().make_usize();
                let actual = self.temp_place(usize_ty);

                // Assign `actual = length(place)`
                let value = self.storage.push_rvalue(RValue::Len(place));
                self.control_flow_graph.push_assign(block, actual.clone(), value, span);

                // @@Todo: can we not just use the `value` directly, there should be no
                // dependency on it in other places, and it will always be a
                // `usize`.
                let actual_operand = self.storage.push_rvalue(RValue::Use(actual));

                // Now, we generate a temporary for the expected length, and then
                // compare the two.
                let const_len =
                    Const::Int(CONSTANT_MAP.create_int_constant(IntConstant::from(len)));
                let expected = self.storage.push_rvalue(RValue::Const(const_len));

                let [success, fail] = *target_blocks else {
                    panic!("expected two target blocks for `Len` test");
                };

                self.compare(block, success, fail, op, actual_operand, expected, span);
            }
        }
    }

    /// Generate IR for a comparison operation with a specified comparison
    /// [BinOp]. This will take in the two [RValueId] operands, push a
    /// [RValue::BinaryOp], and then insert a [TerminatorKind::Switch] which
    /// determines where the control flow goes based on the result of the
    /// comparison.
    pub(super) fn compare(
        &mut self,
        block: BasicBlock,
        success: BasicBlock,
        fail: BasicBlock,
        op: BinOp,
        lhs: RValueId,
        rhs: RValueId,
        span: Span,
    ) {
        debug_assert!(op.is_comparator());

        let bool_ty = self.storage.ty_store().make_bool();
        let result = self.temp_place(bool_ty);

        // Push an assignment with the result of the comparison, i.e. `result = op(lhs,
        // rhs)`
        let value = self.storage.push_rvalue(RValue::BinaryOp(op, lhs, rhs));
        self.control_flow_graph.push_assign(block, result.clone(), value, span);

        // Then insert the switch statement, which determines where the cfg goes based
        // on if the comparison was true or false.
        self.control_flow_graph.terminate(
            block,
            span,
            // @@Todo: make `Place` copy!
            TerminatorKind::make_if(result, success, fail, self.storage),
        );
    }

    /// Try to add any match pairs of the [Candidate] to the particular
    /// `options` of a [TestKind::SwitchInt].
    pub(super) fn add_variants_to_switch(
        &mut self,
        test_place: &PlaceBuilder,
        candidate: &Candidate,
        variants: &mut FixedBitSet,
    ) -> bool {
        // Find the common matching place between the candidate and this
        // value, if there is none then we cannot merge these togegher.
        let Some(match_pair) = candidate.pairs.iter().find(|pair| pair.place == *test_place) else {
            return false;
        };

        // See if the underlying pattern is a variant, and if so add it to
        // the variants...
        self.tcx.pat_store.map_fast(match_pair.pat, |pat| {
            match pat {
                // @@Todo: when we switch over to the knew pattern representation, it
                //         should be a lot easier to deduce which variant is being specified
                //         here.
                Pat::Access(AccessPat { subject, property }) => {
                    // Get the type of the subject, and then compute the
                    // variant index of the property.
                    let ty = self.ty_of_pat(*subject);

                    self.map_on_adt(ty, |adt, _| {
                        let variant_index = adt.variant_idx(property).unwrap();
                        variants.insert(variant_index);
                        true
                    })
                }

                // We don't know how to map anything else.
                _ => false,
            }
        })
    }

    /// Try to add any [Candidate]s that are also matching on a particular
    /// variant.
    pub(super) fn add_cases_to_switch(
        &mut self,
        test_place: &PlaceBuilder,
        candidate: &Candidate,
        ty: IrTyId,
        options: &mut IndexMap<Const, u128>,
    ) -> bool {
        let Some(match_pair) = candidate.pairs.iter().find(|mp| mp.place == *test_place) else {
            return false;
        };

        self.tcx.pat_store.map_fast(match_pair.pat, |pat| {
            match pat {
                Pat::Lit(term) => {
                    let (constant, value) = evaluate_int_lit_term(*term, self.tcx);

                    options.entry(constant).or_insert(value);
                    true
                }
                Pat::Range(pat) => {
                    // Check if there is at least one value that is not
                    // contained within the r
                    self.values_not_contained_in_range(pat, options).unwrap_or(false)
                }
                // We either don't know how to map these, or they should of been mapped
                // by `add_variants_to_switch`.
                Pat::Binding(_)
                | Pat::Access(_)
                | Pat::Const(_)
                | Pat::Tuple(_)
                | Pat::Mod(_)
                | Pat::Constructor(_)
                | Pat::List(_)
                | Pat::Spread(_)
                | Pat::Or(_)
                | Pat::If(_)
                | Pat::Wild => false,
            }
        })
    }

    /// Check if there is at least one value that is not contained within the
    /// range. If there is, then we can add it to the options.
    fn values_not_contained_in_range(
        &mut self,
        pat: &RangePat,
        options: &IndexMap<Const, u128>,
    ) -> Option<bool> {
        let const_range = ConstRange::from_range(pat, self.tcx);

        // Iterate over all of the options and check if the
        // value is contained in the constant range.
        for &value in options.keys() {
            if const_range.contains(value)? {
                return Some(false);
            }
        }

        Some(true)
    }
}