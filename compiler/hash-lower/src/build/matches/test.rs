//! Definitions for [Test]s that is used to represent what kind
//! of test needs to be performed on a particular set of candidates
//! when deciding where to jump to within the decision tree.
#![allow(clippy::too_many_arguments)]

use std::cmp::Ordering;

use fixedbitset::FixedBitSet;
use hash_ast::ast::{self, AstNodeId};
use hash_ir::{
    ir::{
        BasicBlock, BinOp, Const, Operand, PlaceProjection, RValue, SwitchTargets, TerminatorKind,
    },
    ty::{AdtId, IrTy, IrTyId, ToIrTy, VariantIdx, COMMON_IR_TYS},
};
use hash_reporting::macros::panic_on_span;
use hash_source::constant::{IntConstant, IntConstantValue, InternedInt};
use hash_storage::store::statics::CoreStoreId;
use hash_tir::{
    args::PatArgsId,
    atom_info::ItemInAtomInfo,
    control::IfPat,
    data::CtorPat,
    environment::env::AccessToEnv,
    lits::LitPat,
    params::ParamIndex,
    pats::{Pat, PatId, RangePat, Spread},
};
use hash_utils::indexmap::IndexMap;

use super::{
    candidate::{Candidate, MatchPair},
    const_range::ConstRange,
};
use crate::build::{place::PlaceBuilder, BodyBuilder};

/// Convert a [LitPat] into a [Const] value.
fn constify_lit_pat(term: &LitPat) -> Const {
    match term {
        LitPat::Int(lit) => Const::Int(lit.interned_value()),
        LitPat::Str(lit) => Const::Str(lit.interned_value()),
        LitPat::Char(lit) => Const::Char(lit.value()),
    }
}

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
        len: u64,

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
    pub origin: AstNodeId,
}

impl Test {
    /// Return the total amount of targets that a particular
    /// [Test] yields.
    pub(super) fn targets(&self) -> usize {
        match self.kind {
            TestKind::Switch { adt, .. } => {
                // The switch will not (necessarily) generate branches
                // for all of the variants, so we have a target for each
                // variant, and an additional target for the `otherwise` case.
                adt.borrow().variants.len() + 1
            }
            TestKind::SwitchInt { ty, ref options } => {
                ty.map(|ty| {
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

impl<'tcx> BodyBuilder<'tcx> {
    pub(super) fn test_or_pat(
        &mut self,
        candidate: &mut Candidate,
        otherwise: &mut Option<BasicBlock>,
        place_builder: &PlaceBuilder,
        pats: &[PatId],
        or_origin: AstNodeId,
    ) {
        let mut or_candidates: Vec<_> = pats
            .iter()
            .map(|pat| {
                Candidate::new(
                    self.span_of_pat(*pat),
                    *pat,
                    place_builder,
                    candidate.has_guard || pat.borrow().is_if(),
                )
            })
            .collect();

        let mut or_candidates_ref: Vec<_> = or_candidates.iter_mut().collect();

        let otherwise = if candidate.otherwise_block.is_some() {
            &mut candidate.otherwise_block
        } else {
            otherwise
        };

        // Perform the algorithm on these or-pats, and then attempt
        // to simplify anything trivial, and assume the starting block
        // is the pre-binding block of the overall candidate.
        self.match_candidates(
            or_origin,
            candidate.pre_binding_block.unwrap(),
            otherwise,
            &mut or_candidates_ref,
        );
        self.merge_sub_candidates(candidate, or_origin);
    }

    /// Create a [Test] from a [MatchPair]. If this function is called
    /// on a un-simplified pattern, then this breaks an invariant and the
    /// function will panic.
    pub(super) fn test_match_pair(&mut self, pair: &MatchPair) -> Test {
        let origin = self.span_of_pat(pair.pat);

        // Emit a test for a literal kind of pattern, here we also consider
        // constants as being literals.
        let emit_const_test = |value: Const, ty: IrTyId| {
            // If it is not an integral constant, we use an `Eq` test. This will
            // happen when the constant is either a float or a string.
            if value.is_switchable() {
                Test { kind: TestKind::SwitchInt { ty, options: Default::default() }, origin }
            } else {
                Test { kind: TestKind::Eq { ty, value }, origin }
            }
        };

        match *pair.pat.value() {
            Pat::Ctor(pat) => {
                let ty_id = self.ty_id_from_tir_pat(pair.pat);

                ty_id.map(|ty| match ty {
                    IrTy::Bool => {
                        // Constify the bool literal
                        let value =
                            if pat.ctor.1 == 0 { Const::Bool(true) } else { Const::Bool(false) };
                        emit_const_test(value, ty_id)
                    }
                    IrTy::Adt(id) => {
                        let (variant_count, adt) = id.map(|adt| {
                            // Structs can be simplified...
                            if adt.flags.is_struct() {
                                panic_on_span!(
                                    origin.span(),
                                    self.source_map(),
                                    "attempt to test simplify-able pattern, `{}`",
                                    (pair.pat)
                                )
                            }

                            (adt.variants.len(), *id)
                        });

                        Test {
                            kind: TestKind::Switch {
                                adt,
                                options: FixedBitSet::with_capacity(variant_count),
                            },
                            origin,
                        }
                    }
                    _ => unreachable!("non-bool, non-adt type in test_match_pair"),
                })
            }
            Pat::Lit(ref lit) => {
                let value = constify_lit_pat(lit);
                let ty = self.ty_id_from_tir_pat(pair.pat);

                // If it is not an integral constant, we use an `Eq` test. This will
                // happen when the constant is either a float or a string.
                if value.is_switchable() {
                    Test { kind: TestKind::SwitchInt { ty, options: Default::default() }, origin }
                } else {
                    Test { kind: TestKind::Eq { ty, value }, origin }
                }
            }
            Pat::Range(ref range_pat) => {
                let ty = self.ty_id_from_tir_pat(pair.pat);
                Test {
                    kind: TestKind::Range { range: ConstRange::from_range(range_pat, ty, self) },
                    origin,
                }
            }
            Pat::Array(array_pat) => {
                let (prefix, suffix, rest) = array_pat.into_parts();

                let len = (prefix.len() + suffix.len()) as u64;
                let op = if rest.is_some() { BinOp::GtEq } else { BinOp::Eq };

                Test { kind: TestKind::Len { len, op }, origin }
            }
            Pat::If(IfPat { pat, .. }) => {
                self.test_match_pair(&MatchPair { pat, place: pair.place.clone() })
            }
            Pat::Or(_) => panic_on_span!(
                origin.span(),
                self.source_map(),
                "or patterns should be handled by `test_or_pat`"
            ),
            Pat::Tuple(_) | Pat::Binding(_) => {
                panic_on_span!(
                    origin.span(),
                    self.source_map(),
                    "attempt to test simplify-able pattern, `{}`",
                    (pair.pat)
                )
            }
        }
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

        let pat_ty = self.get_inferred_ty(pair.pat);

        match (&test.kind, *pair.pat.value()) {
            (TestKind::Switch { adt, .. }, Pat::Ctor(CtorPat { ctor, ctor_pat_args, .. })) => {
                // If we are performing a variant switch, then this informs
                // variant patterns, bu nothing else.
                let test_adt = self.ty_id_from_tir_ty(pat_ty);
                let variant_index = test_adt.borrow().as_adt().map(|adt| {
                    // If this is a struct, then we don't do anything
                    // since we're expecting an enum. Although, this case shouldn't happen?
                    if adt.flags.is_struct() {
                        return None;
                    }

                    Some(VariantIdx::from_usize(ctor.1))
                })?;

                self.candidate_after_variant_switch(
                    pair_index,
                    *adt,
                    variant_index,
                    Some(ctor_pat_args),
                    candidate,
                );

                Some(variant_index.index())
            }

            (TestKind::Switch { .. }, _) => None,

            // The `bool` case
            (TestKind::SwitchInt { ty, ref options }, Pat::Ctor(CtorPat { ctor, .. })) => {
                // We can't really do anything here since we can't compare them with
                // the switch.
                if !ty.borrow().is_switchable() {
                    unreachable!("switch_int test for constructor pat with non-switchable type");
                }

                let value = if ctor.1 == 0 { Const::Bool(true) } else { Const::Bool(false) };
                let index = options.get_index_of(&value).unwrap();

                // remove the candidate from the pairs
                candidate.pairs.remove(pair_index);
                Some(index)
            }

            // When we are performing a switch over integers, then this informs integer
            // equality, but nothing else, @@Improve: we could use the Pat::Range to rule
            // some things out.
            (TestKind::SwitchInt { ty, ref options }, Pat::Lit(lit)) => {
                // We can't really do anything here since we can't compare them with
                // the switch.
                if !ty.borrow().is_switchable() {
                    return None;
                }

                // @@Todo: when we switch to new patterns, we can look this up without
                // the additional evaluation. However, we might need to modify the `Eq`
                // on `ir::Const` to actually check if integer values are equal.
                let value = self.evaluate_lit_pat(lit).0;
                let index = options.get_index_of(&value).unwrap();

                // remove the candidate from the pairs
                candidate.pairs.remove(pair_index);
                Some(index)
            }
            (TestKind::SwitchInt { ty, ref options }, Pat::Range(ref range_pat)) => {
                let not_contained =
                    self.values_not_contained_in_range(range_pat, *ty, options).unwrap_or(false);

                // If no switch values are contained within this range, so that pattern can only
                // be matched if the test fails.
                not_contained.then(|| options.len())
            }
            (TestKind::SwitchInt { .. }, _) => None,

            (TestKind::Len { len: test_len, op: BinOp::Eq }, Pat::Array(list_pat)) => {
                let (prefix, suffix, rest) = list_pat.into_parts();
                let pat_len = (prefix.len() + suffix.len()) as u64;
                let ty = self.ty_id_from_tir_pat(pair.pat);

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
            (TestKind::Len { len: test_len, op: BinOp::GtEq }, Pat::Array(list_pat)) => {
                let (prefix, suffix, rest) = list_pat.into_parts();
                let pat_len = (prefix.len() + suffix.len()) as u64;

                let ty = self.ty_id_from_tir_pat(pair.pat);

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

            (TestKind::Range { range }, Pat::Range(ref range_pat)) => {
                let actual_range = ConstRange::from_range(range_pat, range.ty, self);

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
                let (value, _) = self.evaluate_lit_pat(lit_pat);

                // If the `value` is not contained in the testing range, so the `value` can be
                // matched only if the test fails.
                if let Some(false) = range.contains(value) {
                    Some(1)
                } else {
                    None
                }
            }
            (TestKind::Range { .. }, _) => None,
            (TestKind::Eq { .. } | TestKind::Len { .. }, pat) => {
                // If we encounter here an or-pattern, then we need to return
                // from here because we will panic if we continue down this
                // branch, since the `test()` only expects fully simplified
                // patterns.
                if pat.is_or() {
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
        }
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
        rest: Option<Spread>,
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

    /// Perform a downcast on the given candidate, and adjust the candidate
    /// sub-patterns if they exist on the variant. In principle, this means that
    /// each sub-pattern now references the downcast place of the enum.
    fn candidate_after_variant_switch(
        &mut self,
        pair_index: usize,
        adt: AdtId,
        variant_index: VariantIdx,
        sub_patterns: Option<PatArgsId>,
        candidate: &mut Candidate,
    ) {
        let pair = candidate.pairs.remove(pair_index);

        // we need to compute the subsequent match pairs after the downcast
        // and add them to the candidate.
        let downcast_place = pair.place.downcast(variant_index);

        // Only deal with sub-patterns if they exist on the variant.
        if let Some(sub_pats) = sub_patterns {
            let consequent_pairs: Vec<_> = adt.map(|adt| {
                let variant = &adt.variants[variant_index];

                sub_pats
                    .borrow()
                    .borrow()
                    .iter()
                    .map(|arg| {
                        let field_index = match arg.target {
                            ParamIndex::Name(name) => variant.field_idx(name).unwrap(),
                            ParamIndex::Position(index) => index,
                        };

                        let place =
                            downcast_place.clone_project(PlaceProjection::Field(field_index));
                        MatchPair { place, pat: arg.pat.assert_pat() }
                    })
                    .collect()
            });

            candidate.pairs.extend(consequent_pairs);
        }
    }

    /// This function is responsible for generating the code for the specified
    /// [Test].
    pub(super) fn perform_test(
        &mut self,
        subject_origin: AstNodeId,
        block: BasicBlock,
        place_builder: &PlaceBuilder,
        test: &Test,
        make_target_blocks: impl FnOnce(&mut Self) -> Vec<BasicBlock>,
    ) {
        // Build the place from the provided place builder
        let place = place_builder.clone().into_place();
        let span = test.origin;

        match test.kind {
            TestKind::Switch { adt, options: ref variants } => {
                let target_blocks = make_target_blocks(self);
                let (variant_count, discriminant_ty) =
                    adt.map(|adt| (adt.variants.len(), adt.discriminant_ty()));

                // Assert that the number of variants is the same as the number of
                // target blocks.
                debug_assert_eq!(variant_count + 1, target_blocks.len());

                let otherwise_block = target_blocks.last().copied();

                // Here we want to create a switch statement that will match on all of the
                // specified discriminants of the ADT.
                let discriminant_ty = discriminant_ty.to_ir_ty();
                let targets = SwitchTargets::new(
                    adt.map(|adt| {
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
                let value = RValue::Discriminant(place);
                self.control_flow_graph.push_assign(block, discriminant_tmp, value, subject_origin);

                // then terminate this block with the `switch` terminator
                self.control_flow_graph.terminate(
                    block,
                    span,
                    TerminatorKind::Switch { value: discriminant_tmp.into(), targets },
                );
            }
            TestKind::SwitchInt { ty, ref options } => {
                let target_blocks = make_target_blocks(self);

                let terminator_kind = if ty.map(|ty| *ty == IrTy::Bool) {
                    debug_assert!(options.len() == 2);

                    let [first_block, second_block] = *target_blocks else {
                        panic!("expected two target blocks for boolean switch");
                    };

                    let (true_block, false_block) = match options[0] {
                        1 => (first_block, second_block),
                        0 => (second_block, first_block),
                        _ => panic!("expected boolean switch to have only two options"),
                    };

                    TerminatorKind::make_if(place.into(), true_block, false_block)
                } else {
                    debug_assert_eq!(options.len() + 1, target_blocks.len());
                    let otherwise_block = target_blocks.last().copied();

                    let targets = SwitchTargets::new(
                        options.values().copied().zip(target_blocks),
                        ty,
                        otherwise_block,
                    );

                    TerminatorKind::Switch { value: place.into(), targets }
                };

                self.control_flow_graph.terminate(block, span, terminator_kind);
            }
            TestKind::Eq { ty, value } => {
                let (is_str, is_scalar) = ty.map(|ty| (matches!(ty, IrTy::Str), ty.is_scalar()));

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

                    let expected = Operand::Const(value.into());
                    let actual = place.into();

                    self.compare(block, success, fail, BinOp::Eq, expected, actual, span);
                } else {
                    // @@Todo: here we essentially have to make a call to some alternative
                    //         equality mechanism since the [BinOp::EqEq] cannot handle
                    //         non-scalar types.
                    unimplemented!("non-scalar comparisons not yet implemented")
                }
            }
            TestKind::Range { range: ConstRange { lo, hi, end, .. } } => {
                let lb_success = self.control_flow_graph.start_new_block();
                let target_blocks = make_target_blocks(self);

                let lo = Operand::Const(lo.into());
                let hi = Operand::Const(hi.into());
                let val = place.into();

                let [success, fail] = *target_blocks else {
                    panic!("expected two target blocks for `Range` test");
                };

                // So here, we generate the control flow checks for the range comparison.
                // Firstly, we generate the check to see if the `value` is less
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
                    ast::RangeEnd::Included => BinOp::LtEq,
                    ast::RangeEnd::Excluded => BinOp::Lt,
                };

                self.compare(lb_success, success, fail, op, val, hi, span);
            }
            TestKind::Len { len, op } => {
                let target_blocks = make_target_blocks(self);

                let usize_ty = COMMON_IR_TYS.usize;
                let actual = self.temp_place(usize_ty);

                // Assign `actual = length(place)`
                let value = RValue::Len(place);
                self.control_flow_graph.push_assign(block, actual, value, span);

                // @@Todo: can we not just use the `value` directly, there should be no
                // dependency on it in other places, and it will always be a
                // `usize`.
                let actual = actual.into();

                // Now, we generate a temporary for the expected length, and then
                // compare the two.
                let const_len = Const::Int(InternedInt::from(IntConstant {
                    value: IntConstantValue::U64(len),
                    suffix: None,
                }));
                let expected = Operand::Const(const_len.into());

                let [success, fail] = *target_blocks else {
                    panic!("expected two target blocks for `Len` test");
                };

                self.compare(block, success, fail, op, actual, expected, span);
            }
        }
    }

    /// Generate IR for a comparison operation with a specified comparison
    /// [BinOp]. This will take in the two [Operand]s, push a
    /// [RValue::BinaryOp], and then insert a [TerminatorKind::Switch] which
    /// determines where the control flow goes based on the result of the
    /// comparison.
    pub(super) fn compare(
        &mut self,
        block: BasicBlock,
        success: BasicBlock,
        fail: BasicBlock,
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
        origin: AstNodeId,
    ) {
        debug_assert!(op.is_comparator());

        let bool_ty = COMMON_IR_TYS.bool;
        let result = self.temp_place(bool_ty);

        // Push an assignment with the result of the comparison, i.e. `result = op(lhs,
        // rhs)`
        let operands = Box::new((lhs, rhs));
        let value = RValue::BinaryOp(op, operands);
        self.control_flow_graph.push_assign(block, result, value, origin);

        // Then insert the switch statement, which determines where the cfg goes based
        // on if the comparison was true or false.
        self.control_flow_graph.terminate(
            block,
            origin,
            TerminatorKind::make_if(result.into(), success, fail),
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
        // value, if there is none then we cannot merge these together.
        let Some(match_pair) = candidate.pairs.iter().find(|pair| pair.place == *test_place) else {
            return false;
        };

        // See if the underlying pattern is a variant, and if so add it to
        // the variants...
        match *match_pair.pat.value() {
            Pat::Ctor(CtorPat { ctor, .. }) => {
                variants.insert(ctor.1);
                true
            }

            // We don't know how to map anything else.
            _ => false,
        }
    }

    /// Try to add any [Candidate]s that are also matching on a particular
    /// variant.
    pub(super) fn add_cases_to_switch(
        &mut self,
        test_place: &PlaceBuilder,
        candidate: &Candidate,
        options: &mut IndexMap<Const, u128>,
    ) -> bool {
        let Some(match_pair) = candidate.pairs.iter().find(|mp| mp.place == *test_place) else {
            return false;
        };

        match *match_pair.pat.value() {
            Pat::Lit(term) => {
                let (constant, value) = self.evaluate_lit_pat(term);
                options.entry(constant).or_insert(value);
                true
            }
            Pat::Range(ref pat) => {
                // Check if there is at least one value that is not
                // contained within the range.
                let ty = self.ty_id_from_tir_pat(match_pair.pat);
                self.values_not_contained_in_range(pat, ty, options).unwrap_or(false)
            }

            // Boolean type...
            Pat::Ctor(ctor_pat) => {
                // If the constructor is `1` then we know that it is `true`, this is defined
                // in: compiler/hash-intrinsics/src/primitives.rs
                let (constant, value) = if ctor_pat.ctor.1 == 0 {
                    (Const::Bool(true), 1)
                } else {
                    (Const::Bool(false), 0)
                };

                options.entry(constant).or_insert(value);
                true
            }

            // We either don't know how to map these, or they should of been mapped
            // by `add_variants_to_switch`.
            Pat::Binding(_) | Pat::Tuple(_) | Pat::Array(_) | Pat::Or(_) | Pat::If(_) => false,
        }
    }

    /// Check if there is at least one value that is not contained within the
    /// range. If there is, then we can add it to the options.
    fn values_not_contained_in_range(
        &mut self,
        pat: &RangePat,
        ty: IrTyId,
        options: &IndexMap<Const, u128>,
    ) -> Option<bool> {
        let const_range = ConstRange::from_range(pat, ty, self);

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
