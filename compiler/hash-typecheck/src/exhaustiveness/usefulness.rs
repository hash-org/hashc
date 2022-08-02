//! Hash Typechecker pattern exhaustiveness module. This module contains all
//! of the machinery that is responsible for validating the exhaustiveness and
//! usefulness of patterns.
//!
//! Usefulness and exhaustiveness are inherently linked concepts, and are
//! computed in at the same time. In terms of `usefulness` we compute that if a
//! specified pattern `p` is useful in regards to a row of patterns `v` which
//! precede `p`. In other words, will this pattern `p` be ever reached if the
//! patterns `v` are specified before it. Usefulness determines if certain
//! branches in a `match` statement or other constructs that utilise patterns
//! will ever be matched.
//!
//! Exhaustiveness is similar to usefulness, but addresses the question of will
//! the provided row of patterns `v` cover all variants of some subject type.
//! For example, in the `match` block:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(_) => print("there is a number");
//!     None => print("there is no number");
//! };
//! ```
//!
//! So in this example, for `x` which is of type `Option<i32>`, will the
//! patterns: [`Some(_)`, `None`] cover all cases of `Option<i32>`. In this
//! situation yes, because both variants and their inner constructors because of
//! the wildcard `_`. However, a case where this property does not hold can be
//! easily constructed:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(3) => print("The number is 3!");
//!     None => print("there is no number");
//! };
//! ```
//!
//! Well here, we can come up with cases which the pattern set does not cover,
//! for example `Some(4)`. Therefore, the exhaustiveness check will conclude
//! that the provided pattern vector is not exhaustive and misses some cases.
//!
//! The implementation of this algorithm is based on the research paper:
//! http://moscova.inria.fr/~maranget/papers/warn/warn.pdf, and is heavily
//! inspired by the Rust Compiler implementation:
//! <https://github.com/rust-lang/rust/tree/master/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs>
use std::iter::once;

use super::{
    construct::Constructor, deconstruct::DeconstructedPat, fields::Fields, matrix::Matrix,
    stack::PatStack, AccessToUsefulnessOps,
};
use crate::{
    exhaustiveness::structures::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, DeconstructedPatId, TermId},
        AccessToStorage, StorageRef,
    },
};
use hash_source::location::Span;
use hash_utils::stack::ensure_sufficient_stack;
use itertools::Itertools;
use smallvec::smallvec;

#[derive(Debug)]
pub struct Witness(pub Vec<DeconstructedPatId>);

impl Witness {
    /// Asserts that the witness contains a single pattern, and returns it.   
    pub fn single_pattern(self) -> DeconstructedPatId {
        assert_eq!(self.0.len(), 1);

        self.0.into_iter().next().unwrap()
    }
}

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
            //            A single (empty) witness of reachability.
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: true },
        }
    }

    /// Create a `useless` [Usefulness] report.
    pub fn new_not_useful(preference: MatchArmKind) -> Self {
        match preference {
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
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
    pub(crate) pat: DeconstructedPatId,
    pub(crate) has_guard: bool,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Clone, Debug)]
pub(crate) enum Reachability {
    /// The arm is reachable. This additionally carries a set of or-pattern
    /// branches that have been found to be unreachable despite the overall
    /// arm being reachable. Used only in the presence of or-patterns,
    /// otherwise it stays empty.
    Reachable(Vec<Span>),
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
    pub(crate) non_exhaustiveness_witnesses: Vec<DeconstructedPatId>,
}

pub struct UsefulnessOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for UsefulnessOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> UsefulnessOps<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Constructs a partial witness for a pattern given a list of
    /// patterns expanded by the specialization step.
    ///
    /// When a pattern P is discovered to be useful, this function is used
    /// bottom-up to reconstruct a complete witness, e.g., a pattern P' that    
    /// covers a subset of values, V, where each value in that set is not
    /// covered by any previously used patterns and is covered by the
    /// pattern P'. Examples:
    ///
    /// left_ty: tuple of 3 elements
    /// pats: [10, 20, _]           => (10, 20, _)
    ///
    /// left_ty: struct X { a: (bool, &'static str), b: usize}
    /// pats: [(false, "foo"), 42]  => X { a: (false, "foo"), b: 42 }
    fn apply_constructor_on_witness(
        &self,
        ctx: PatCtx,
        mut witness: Witness,
        ctor: ConstructorId,
    ) -> Witness {
        let pat = {
            let len = witness.0.len();
            let arity = self.constructor_ops().arity(ctx, ctor);

            let pats = witness.0.drain((len - arity)..).rev();
            let fields = Fields::from_iter(pats);

            DeconstructedPat::new(ctor, fields, ctx.ty, Span::dummy())
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
        &mut self,
        ctx: PatCtx,
        usefulness: Usefulness,
        matrix: &Matrix, // used to compute missing ctors
        ctor_id: ConstructorId,
    ) -> Usefulness {
        match usefulness {
            Usefulness::NoWitnesses { .. } => usefulness,
            Usefulness::WithWitnesses(ref witnesses) if witnesses.is_empty() => usefulness,
            Usefulness::WithWitnesses(witnesses) => {
                let new_witnesses = if self
                    .constructor_store()
                    .map_unsafe(ctor_id, |ctor| matches!(ctor, Constructor::Missing))
                {
                    // We got the special `Missing` constructor, so each of the missing constructors
                    // gives a new  pattern that is not caught by the match. We
                    // list those patterns.
                    let mut wildcard = self.split_wildcard_ops().from(ctx);

                    let reader = self.reader();
                    let ctors = matrix.heads().map(|id| reader.get_deconstructed_pat(id).ctor());

                    self.split_wildcard_ops().split(ctx, &mut wildcard, ctors);

                    // Get all the missing constructors for the current type
                    let new_pats = self
                        .split_wildcard_ops()
                        .iter_missing(&wildcard)
                        .into_iter()
                        .map(|missing_ctor| {
                            let pat = self.deconstruct_pat_ops().wild_from_ctor(ctx, missing_ctor);
                            self.deconstructed_pat_store().create(pat)
                        })
                        .collect_vec();

                    // Firstly, read all of the patterns stored in the current witness
                    // and clone them whilst forgetting
                    // the reachability
                    let t: Vec<_> = witnesses
                        .into_iter()
                        .flat_map(|witness| {
                            new_pats.iter().map(move |pat| {
                                witness.0.clone().iter().copied().chain(once(*pat)).collect_vec()
                            })
                        })
                        .collect();

                    let mut new_witnesses = vec![];

                    for inner in t {
                        let mut new_inner = vec![];

                        for pat in inner {
                            let reader = self.reader();

                            let new_pat =
                                reader.get_deconstructed_pat(pat).clone_and_forget_reachability();

                            let new_pat = self.deconstructed_pat_store().create(new_pat);
                            new_inner.push(new_pat);
                        }

                        new_witnesses.push(Witness(new_inner))
                    }

                    new_witnesses
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
    ///   (0) We don't exit early if the pattern matrix has zero rows. We just
    ///       continue to recurse over columns.
    ///   (1) all_constructors will only return constructors that are statically
    ///       possible. E.g., it will only return `Ok` for `Result<T, !>`.
    ///
    /// This finds whether a (row) vector `v` of patterns is 'useful' in
    /// relation to a set of such vectors `m` - this is defined as there
    /// being a set of inputs that will match `v` but not any of the sets in
    /// `m`.
    ///
    /// All the patterns at each column of the `matrix ++ v` matrix must have
    /// the same type.
    ///
    /// This is used both for reachability checking (if a pattern isn't useful
    /// in relation to preceding patterns, it is not reachable) and
    /// exhaustiveness checking (if a wildcard pattern is useful in relation
    /// to a matrix, the matrix isn't exhaustive).
    ///
    /// `is_under_guard` is used to inform if the pattern has a guard. If it
    /// has one it must not be inserted into the matrix. This shouldn't be
    /// relied on for soundness.
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

        let ty = head.ty();
        let span = head.span();

        // Create a new `PatCtx`, based on on the provided parameters
        let ctx = PatCtx::new(ty, span, is_top_level);
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

                // @@Todo: deal with `if-guards` on the patterns themselves.
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
            let v_ctor = head.ctor();

            // @@Todo: we should check that int ranges don't overlap here, in case
            // they're partially covered by other ranges.
            let reader = self.reader();

            let ctors = matrix.heads().map(|id| reader.get_deconstructed_pat(id).ctor());

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
            self.deconstructed_pat_store().update_unsafe(v.head(), |item| item.set_reachable());
        }

        report
    }

    pub(crate) fn compute_match_usefulness(
        &mut self,
        _subject: TermId,
        arms: &[MatchArm],
    ) -> UsefulnessReport {
        let mut matrix = Matrix::empty();

        // Compute usefulness for each arm in the match
        let arm_usefulness: Vec<_> = arms
            .iter()
            .copied()
            .map(|arm| {
                let v = PatStack::singleton(arm.pat);
                self.is_useful(&matrix, &v, MatchArmKind::Real, arm.has_guard, true);

                // We still compute the usefulness of if-guard patterns, but we don't
                // add them into the matrix since we can't guarantee that they
                // yield all possible conditions
                if !arm.has_guard {
                    self.matrix_ops().push(&mut matrix, v);
                }

                let reader = self.reader();
                let pat = reader.get_deconstructed_pat(arm.pat);

                let reachability = if pat.is_reachable() {
                    Reachability::Reachable(self.deconstruct_pat_ops().unreachable_spans(&pat))
                } else {
                    Reachability::Unreachable
                };
                (arm, reachability)
            })
            .collect();

        // @@Todo: create the wildcard, using an arena
        // let wildcard = ...;
        // let v = PatStack::singleton(v);

        let v = PatStack::from_vec(smallvec![]);

        let usefulness = self.is_useful(&matrix, &v, MatchArmKind::ExhaustiveWildcard, false, true);

        // It should not be possible to not get any witnesses since we're matching
        // on a wildcard, the base case is that `pats` is empty and thus the
        // set of patterns that are provided in the match block are exhaustive.
        let non_exhaustiveness_witnesses = match usefulness {
            Usefulness::WithWitnesses(pats) => {
                pats.into_iter().map(|w| w.single_pattern()).collect()
            }
            Usefulness::NoWitnesses { .. } => panic!(),
        };

        UsefulnessReport { arm_usefulness, non_exhaustiveness_witnesses }
    }
}
