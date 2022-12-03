//! Definitions for [Test]s that is used to represent what kind
//! of test needs to be performed on a particular set of candidates
//! when deciding where to jump to within the decision tree.

use fixedbitset::FixedBitSet;
use hash_ast::ast::{ConstructorPat, RangeEnd};
use hash_ir::{
    ir::{BasicBlock, BinOp, Const},
    ty::{AdtId, IrTy, IrTyId, VariantIdx},
};
use hash_source::location::Span;
use hash_types::pats::{AccessPat, Pat, PatId};
use hash_utils::store::Store;
use indexmap::IndexMap;

use super::candidate::{self, Candidate};
use crate::build::{place::PlaceBuilder, Builder};

/// A [Test] represents a test that will be carried out on a
/// a particular [Candidate].
pub(super) struct Test {
    /// The kind of test that is being performed on the candidate
    kind: TestKind,

    /// The span of where the test occurs, in order to provide richer
    /// information to basic block terminations when actually *performing*
    /// the test
    span: Span,
}

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
    Range { lo: Const, hi: Const, end: RangeEnd },

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

impl<'tcx> Builder<'tcx> {
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
    /// exponential number of tests occurring. (@@Explain).
    ///
    /// To avoid this, we try to ensure that the amount of generated tests is
    /// linear. We
    // / do this by doing a k-way test, which returns an additional "unmatched" set alongside
    /// the matches `k` set. When we encounter a candidate that would present in
    /// more than one of the sets, we put it and all candidates below it in
    /// an "unmatched" set. This ensures that these sets are disjoint, which
    /// means we don't need to perform more than k + 1 tests.
    ///
    /// Once a test is performed, we branch into the appropriate candidate set,
    /// and then recursively call `match_candidates`. These sub-matches are
    /// non-exhaustive (since we discarded the `otherwise` set) - so we
    /// continue with the "unmatched" set with `match_candidates` Using this
    /// approach, we essentially generate an `if-else-if` chain.
    pub(super) fn test_candidates(
        &mut self,
        span: Span,
        candidates: &mut [&mut Candidate],
        block: BasicBlock,
        otherwise: &mut Option<BasicBlock>,
    ) {
        // take the first pattern
        let pair = &candidates.first().unwrap().pairs[0];
        let mut test = self.test_pat(pair.pat);
        let match_place = pair.place.clone();

        // For switch tests, we may want to add additional cases to the
        // test from the available candidates
        match test.kind {
            TestKind::Switch { adt, options: ref mut variants } => {
                for candidate in candidates.iter() {
                    // If we couldn't add a particular candidate, then short-circuit
                    // since we won't be able to add any candidates after.
                    if !self.add_variants_to_switch(&match_place, candidate, variants) {
                        break;
                    }
                }
            }
            TestKind::SwitchInt { ty, ref mut options } => {
                for candidate in candidates.iter() {
                    // If we couldn't add a particular candidate, then short-circuit
                    // since we won't be able to add any candidates after.
                    if !self.add_cases_to_switch(&match_place, candidate, ty, options) {
                        break;
                    }
                }
            }
            _ => {}
        };

        todo!()
    }

    /// Try to add any match pairs of the [Candidate] to the particular
    /// `options` of a [TestKind::SwitchInt].
    fn add_variants_to_switch(
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
                    let ty = self.get_ty_of_pat(*subject);

                    self.storage.ty_store().map_fast(ty, |ty| {
                        let IrTy::Adt(adt) = ty else {
                            unreachable!("expected ADT from subject type of access pattern");
                        };

                        // Add the variant to the options
                        self.storage.adt_store().map_fast(*adt, |adt| {
                            let variant_index = adt.variant_idx(property).unwrap();
                            variants.insert(variant_index);
                            true
                        })
                    })
                }

                // We don't know how to map anything else.
                _ => false,
            }
        })
    }

    /// Try to add any [Candidate]s that are also matching on a particular
    /// variant.
    fn add_cases_to_switch(
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
                Pat::Lit(_) => todo!(),
                Pat::Range(_) => {
                    todo!()
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

    pub(super) fn test_or_pat(
        &mut self,
        candidate: &mut Candidate,
        otherwise: &mut Option<BasicBlock>,
        pats: &[PatId],
    ) {
        todo!()
    }

    pub(super) fn test_pat(&mut self, pat: PatId) -> Test {
        todo!()
    }
}
