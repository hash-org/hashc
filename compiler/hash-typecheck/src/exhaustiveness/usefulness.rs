//! This module contains the entry point for the usefulness and
//! exhaustiveness algorithm that the Hash typechecker uses to
//! verify that patterns are refutable, and match blocks
//! are fully exhaustive.
//!
//! More information about the algorithm and the implementation
//! is detailed within [super].
use std::iter::once;

use hash_types::{pats::PatId, terms::TermId};
use hash_utils::{stack::ensure_sufficient_stack, store::Store};
use itertools::Itertools;

use super::{
    construct::DeconstructedCtor, deconstruct::DeconstructedPat, fields::Fields, matrix::Matrix,
    stack::PatStack, AccessToUsefulnessOps,
};
use crate::{
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        exhaustiveness::{DeconstructedCtorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
};

/// Collection of patterns that were `witnessed` when traversing
/// the provided patterns.
#[derive(Debug)]
pub struct Witness(pub Vec<DeconstructedPatId>);

impl Witness {
    /// Asserts that the witness contains a single pattern, and returns it.
    pub fn single_pat(self) -> DeconstructedPatId {
        assert_eq!(self.0.len(), 1);

        self.0.into_iter().next().unwrap()
    }
}

/// Representation of the result from computing the usefulness of a pattern.
#[derive(Debug)]
pub enum Usefulness {
    /// If we don't care about witnesses, simply remember if the pattern was
    /// useful.
    NoWitnesses { useful: bool },
    /// Carries a list of witnesses of non-exhaustiveness. If empty, indicates
    /// that the whole pattern is unreachable.
    WithWitnesses(Vec<Witness>),
}

impl Usefulness {
    /// Create a `useful` [Usefulness] report.
    pub fn new_useful(preference: MatchArmKind) -> Self {
        match preference {
            // A single (empty) witness of reachability.
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: true },
        }
    }

    /// Create a `useless` [Usefulness] report.
    pub fn new_not_useful(preference: MatchArmKind) -> Self {
        match preference {
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: false },
        }
    }

    /// Check if the [Usefulness] report specifies that the pattern is  useful.
    pub fn is_useful(&self) -> bool {
        match self {
            Usefulness::NoWitnesses { useful } => *useful,
            Usefulness::WithWitnesses(witnesses) => !witnesses.is_empty(),
        }
    }

    /// Combine usefulnesses from two branches. This is an associative
    /// operation.
    pub fn extend(&mut self, other: Self) {
        match (&mut *self, other) {
            (Usefulness::WithWitnesses(_), Usefulness::WithWitnesses(o)) if o.is_empty() => {}
            (Usefulness::WithWitnesses(s), Usefulness::WithWitnesses(o)) if s.is_empty() => {
                *self = Usefulness::WithWitnesses(o)
            }
            (Usefulness::WithWitnesses(s), Usefulness::WithWitnesses(o)) => s.extend(o),
            (
                Usefulness::NoWitnesses { useful: s_useful },
                Usefulness::NoWitnesses { useful: o_useful },
            ) => *s_useful = *s_useful || o_useful,
            _ => unreachable!(),
        }
    }
}

/// Enum used to represent the kind of match arm that is being
/// checked for usefulness. This exists in order to be able to
/// inject a `dummy` match-arm to collect witnesses of patterns
/// that the branch will capture.
#[derive(Debug, Clone, Copy)]
pub enum MatchArmKind {
    /// This is used as a `dummy` kind of arm in order to
    /// detect any witnesses that haven't been picked up when
    /// walking through the the arms of a match block.
    ExhaustiveWildcard,
    /// Normal match arm, has no particular behaviour when
    /// checking the usefulness of the pattern.
    Real,
}

/// The arm of a match expression.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MatchArm {
    /// The pattern must have been lowered through
    /// `check_match::MatchVisitor::lower_pattern`.
    pub(crate) deconstructed_pat: DeconstructedPatId,
    /// Whether the arm has an `if-guard`
    pub(crate) has_guard: bool,
    /// The corresponding [hash_types::Pat] with this
    /// match arm
    pub(crate) id: PatId,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Clone, Debug)]
pub(crate) enum Reachability {
    /// The arm is reachable. This additionally carries a set of or-pattern
    /// branches that have been found to be unreachable despite the overall
    /// arm being reachable. Used only in the presence of or-patterns,
    /// otherwise it stays empty.
    Reachable(Vec<PatId>),
    /// The arm is unreachable.
    Unreachable,
}

/// The output of checking a match for exhaustiveness and arm reachability.
pub(crate) struct UsefulnessReport {
    /// For each arm of the input, whether that arm is reachable after the arms
    /// above it.
    pub(crate) arm_usefulness: Vec<(MatchArm, Reachability)>,
    /// If the match is exhaustive, this is empty. If not, this contains
    /// witnesses for the lack of exhaustiveness.
    pub(crate) non_exhaustiveness_witnesses: Vec<PatId>,
}

pub struct UsefulnessOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for UsefulnessOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> UsefulnessOps<'tc> {
    /// Create a new instance of [UsefulnessOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Constructs a partial witness for a pattern given a list of
    /// patterns expanded by the specialisation step.
    ///
    /// When a pattern P is discovered to be useful, this function is used
    /// bottom-up to reconstruct a complete witness, e.g., a pattern P' that
    /// covers a subset of values, V, where each value in that set is not
    /// covered by any previously used patterns and is covered by the
    /// pattern P'. Examples:
    ///
    /// left_ty: `(u32, u32, u32)`
    /// pats: `[10, 20, _]           => (10, 20, _)`
    ///
    /// left_ty: struct `X := struct(a: (bool, str), b: u32)`
    /// pats: `[(false, "foo"), 42]  => X( a = (false, "foo"), b = 42)`
    fn apply_constructor_on_witness(
        &self,
        ctx: PatCtx,
        mut witness: Witness,
        ctor: DeconstructedCtorId,
    ) -> Witness {
        let pat = {
            let len = witness.0.len();
            let arity = self.constructor_ops().arity(ctx, ctor);

            let pats = witness.0.drain((len - arity)..).rev();
            let fields = Fields::from_iter(pats);

            DeconstructedPat::new(ctor, fields, ctx.ty, None)
        };

        let pat = self.deconstructed_pat_store().create(pat);
        witness.0.push(pat);
        witness
    }

    /// After calculating usefulness after a specialization, call this to
    /// reconstruct a usefulness that makes sense for the matrix
    /// pre-specialization. This new usefulness can then be merged
    /// with the results of specializing with the other constructors.
    fn apply_constructor(
        &self,
        ctx: PatCtx,
        usefulness: Usefulness,
        matrix: &Matrix, // used to compute missing ctors
        ctor_id: DeconstructedCtorId,
    ) -> Usefulness {
        match usefulness {
            Usefulness::NoWitnesses { .. } => usefulness,
            Usefulness::WithWitnesses(ref witnesses) if witnesses.is_empty() => usefulness,
            Usefulness::WithWitnesses(witnesses) => {
                let new_witnesses = if self
                    .constructor_store()
                    .map_fast(ctor_id, |ctor| matches!(ctor, DeconstructedCtor::Missing))
                {
                    // We got the special `Missing` constructor, so each of the missing constructors
                    // gives a new  pattern that is not caught by the match. We
                    // list those patterns.
                    let mut wildcard = self.split_wildcard_ops().from(ctx);

                    let reader = self.reader();
                    let ctors = matrix.heads().map(|id| reader.get_deconstructed_pat(id).ctor);

                    self.split_wildcard_ops().split(ctx, &mut wildcard, ctors);

                    // Get all the missing constructors for the current type
                    let new_pats = self
                        .split_wildcard_ops()
                        .iter_missing(&wildcard)
                        .map(|missing_ctor| {
                            let pat = self.deconstruct_pat_ops().wild_from_ctor(ctx, missing_ctor);
                            self.deconstructed_pat_store().create(pat)
                        })
                        .collect_vec();

                    // Prepare new witnesses by attaching each of the `new_pats` to the end of
                    // old witness `ids`
                    let ids: Vec<_> = witnesses
                        .into_iter()
                        .flat_map(|witness| {
                            new_pats.iter().map(move |pat| {
                                witness.0.clone().iter().copied().chain(once(*pat)).collect_vec()
                            })
                        })
                        .collect();

                    // Now we need to create the new witnesses, so iterate over each of the inner
                    // id collections, and copy them within the store
                    ids.iter()
                        .map(|new_witness_pats| {
                            let reader = self.reader();

                            let copied_pats = new_witness_pats
                                .iter()
                                .map(|pat| {
                                    // Clone and forget the `pat` and then forget that that it is
                                    // reachable
                                    let new_pat = reader.get_deconstructed_pat(*pat);
                                    new_pat.reachable.set(false);

                                    self.deconstructed_pat_store().create(new_pat)
                                })
                                .collect_vec();

                            Witness(copied_pats)
                        })
                        .collect_vec()
                } else {
                    witnesses
                        .into_iter()
                        .map(|witness| self.apply_constructor_on_witness(ctx, witness, ctor_id))
                        .collect()
                };

                Usefulness::WithWitnesses(new_witnesses)
            }
        }
    }

    /// Algorithm from <http://moscova.inria.fr/~maranget/papers/warn/index.html>.
    /// The algorithm from the paper has been modified to correctly handle empty
    /// types. The changes are:
    ///
    ///   (0) We don't exit early if the pattern matrix has zero rows. We just
    ///       continue to recurse over columns.
    ///
    ///   (1) all_constructors will only return constructors that are
    ///       statically possible. E.g., it will only return `Ok` for
    ///       `Result<T, !>`.
    ///
    /// This finds whether a (row) vector `v` of patterns is 'useful' in
    /// relation to a set of such vectors `m` - this is defined as there
    /// being a set of inputs that will match `v` but not any of the sets in
    /// `m`.
    ///
    /// **Note** All the patterns at each column of the `matrix ++ v` matrix
    /// must have the same type. The types must also be simplified at this
    /// stage!
    ///
    /// This is used both for reachability checking (if a pattern isn't useful
    /// in relation to preceding patterns, it is not reachable) and
    /// exhaustiveness checking (if a wildcard pattern is useful in relation
    /// to a matrix, the matrix isn't exhaustive).
    fn is_useful(
        &mut self,
        matrix: &Matrix,
        v: &PatStack,
        arm_kind: MatchArmKind,
        is_under_guard: bool,
        is_top_level: bool,
    ) -> Usefulness {
        let Matrix { patterns: rows, .. } = matrix;

        // The base case. We are pattern-matching on () and the return value is
        // based on whether our matrix has a row or not.
        if v.is_empty() {
            let ret = if rows.is_empty() {
                Usefulness::new_useful(arm_kind)
            } else {
                Usefulness::new_not_useful(arm_kind)
            };

            return ret;
        }

        let reader = self.reader();
        let head = reader.get_deconstructed_pat(v.head());

        let DeconstructedPat { ty, .. } = head;

        // Create a new `PatCtx`, based on on the provided parameters
        let ctx = PatCtx::new(ty, is_top_level);
        let mut report = Usefulness::new_not_useful(arm_kind);

        // If the first pattern is an or-pattern, expand it.
        if self.deconstruct_pat_ops().is_or_pat(&head) {
            // We try each or-pattern branch in turn.
            let mut matrix = matrix.clone();

            for v in self.stack_ops().expand_or_pat(v) {
                let usefulness = ensure_sufficient_stack(|| {
                    self.is_useful(&matrix, &v, arm_kind, is_under_guard, false)
                });

                report.extend(usefulness);

                // @@Investigate: deal with `if-guards` on the patterns themselves.
                //
                // If the pattern has a guard don't add it to the matrix, but otherwise
                // just push it into the matrix, it doesn't matter if it has already
                //  been seen in the current `or` pattern since we want to detect redundant
                // members within the or pattern as well... for example:
                // ``` Ok(_) | Ok(3) => ...; ```
                //
                if !is_under_guard {
                    self.matrix_ops().push(&mut matrix, v);
                }
            }
        } else {
            let reader = self.reader();
            let ctors = matrix.heads().map(|id| reader.get_deconstructed_pat(id).ctor);

            let v_ctor = head.ctor;

            // check that int ranges don't overlap here, in case
            // they're partially covered by other ranges.
            if let DeconstructedCtor::IntRange(range) = reader.get_deconstructed_ctor(v_ctor) {
                if let Some(head_id) = head.id {
                    self.int_range_ops().check_for_overlapping_endpoints(
                        head_id,
                        range,
                        matrix.heads(),
                        matrix.column_count().unwrap_or(0),
                        ty,
                    );
                }
            }

            // We split the head constructor of `v`.
            let split_ctors = self.constructor_ops().split(ctx, v_ctor, ctors);
            let start_matrix = &matrix;

            // For each constructor, we compute whether there's a value that starts with it
            // that would witness the usefulness of `v`.
            for ctor in split_ctors {
                // cache the result of `Fields::wildcards` because it is used a lot.
                let spec_matrix = self.matrix_ops().specialise_ctor(ctx, start_matrix, ctor);

                let v = self.stack_ops().pop_head_constructor(ctx, v, ctor);
                let usefulness = ensure_sufficient_stack(|| {
                    self.is_useful(&spec_matrix, &v, arm_kind, is_under_guard, false)
                });

                let usefulness = self.apply_constructor(ctx, usefulness, start_matrix, ctor);
                report.extend(usefulness);
            }
        }

        if report.is_useful() {
            self.deconstructed_pat_store().modify_fast(v.head(), |item| item.set_reachable());
        }

        report
    }

    /// The entrypoint for the usefulness algorithm. Computes whether a match is
    /// exhaustive and which of its arms are reachable.
    ///
    /// Note: the input patterns must have been lowered through
    /// [super::lower::LowerPatOps]
    pub(crate) fn compute_match_usefulness(
        &mut self,
        subject: TermId,
        arms: &[MatchArm],
    ) -> UsefulnessReport {
        let mut matrix = Matrix::empty();

        // Compute usefulness for each arm in the match
        let arm_usefulness: Vec<_> = arms
            .iter()
            .copied()
            .map(|arm| {
                let v = PatStack::singleton(arm.deconstructed_pat);
                self.is_useful(&matrix, &v, MatchArmKind::Real, arm.has_guard, true);

                // We still compute the usefulness of if-guard patterns, but we don't
                // add them into the matrix since we can't guarantee that they
                // yield all possible conditions
                if !arm.has_guard {
                    self.matrix_ops().push(&mut matrix, v);
                }

                let reader = self.reader();
                let pat = reader.get_deconstructed_pat(arm.deconstructed_pat);

                let reachability = if pat.is_reachable() {
                    Reachability::Reachable(self.deconstruct_pat_ops().unreachable_pats(&pat))
                } else {
                    Reachability::Unreachable
                };
                (arm, reachability)
            })
            .collect();

        let wildcard =
            self.deconstructed_pat_store().create(self.deconstruct_pat_ops().wildcard(subject));
        let v = PatStack::singleton(wildcard);
        let usefulness = self.is_useful(&matrix, &v, MatchArmKind::ExhaustiveWildcard, false, true);

        // It should not be possible to not get any witnesses since we're matching
        // on a wildcard, the base case is that `pats` is empty and thus the
        // set of patterns that are provided in the match block are exhaustive.
        let non_exhaustiveness_witnesses = match usefulness {
            Usefulness::WithWitnesses(pats) => {
                pats.into_iter().map(|w| self.pat_lowerer().construct_pat(w.single_pat())).collect()
            }
            Usefulness::NoWitnesses { .. } => panic!(),
        };

        UsefulnessReport { arm_usefulness, non_exhaustiveness_witnesses }
    }
}
