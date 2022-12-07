//! Definitions for [Test]s that is used to represent what kind
//! of test needs to be performed on a particular set of candidates
//! when deciding where to jump to within the decision tree.

use fixedbitset::FixedBitSet;
use hash_ir::{
    ir::{BasicBlock, BinOp, Const, RValue, SwitchTargets, TerminatorKind},
    ty::{AdtId, IrTy, IrTyId},
    IrStorage,
};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_types::{
    fmt::PrepareForFormatting,
    pats::{AccessPat, IfPat, Pat, PatId, RangePat},
};
use hash_utils::store::Store;
use indexmap::IndexMap;

use super::{
    candidate::{Candidate, MatchPair},
    utils::ConstRange,
};
use crate::build::{
    place::PlaceBuilder,
    ty::{constify_lit_term, evaluate_int_lit_term},
    Builder,
};

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
                    let op = if rest.is_some() { BinOp::GtEq } else { BinOp::EqEq };

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

    pub(super) fn sort_candidate(
        &mut self,
        _match_place: &PlaceBuilder,
        _test: &Test,
        _candidate: &mut Candidate,
    ) -> Option<usize> {
        todo!()
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

                let terminator_kind =
                    if self.storage.ty_store().map_fast(ty, |ty| *ty == IrTy::Bool) {
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
            TestKind::Eq { ty, value } => todo!(),
            TestKind::Range { ref range } => todo!(),
            TestKind::Len { len, op } => todo!(),
        }
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
        options: &mut IndexMap<Const, u128>,
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
