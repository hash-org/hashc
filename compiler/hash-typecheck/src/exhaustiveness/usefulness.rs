use std::{fmt, iter::once};

use hash_source::location::Span;
use hash_utils::stack::ensure_sufficient_stack;
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};

use crate::storage::{primitives::TermId, AccessToStorageMut, StorageRefMut};

use super::deconstruct::{Constructor, DeconstructedPat, Fields, PatCtx, SplitWildcard};

#[derive(Debug)]
pub(crate) struct Witness(Vec<DeconstructedPat>);

impl<'gs, 'ls, 'cd, 's> Witness {
    /// Asserts that the witness contains a single pattern, and returns it.
    fn single_pattern(self) -> DeconstructedPat {
        assert_eq!(self.0.len(), 1);
        self.0.into_iter().next().unwrap()
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
    fn apply_constructor(mut self, mut ctx: PatCtx<'gs, 'ls, 'cd, 's>, ctor: &Constructor) -> Self {
        let pat = {
            let len = self.0.len();
            let arity = ctor.arity(ctx.new_from());

            let pats = self.0.drain((len - arity)..).rev();
            let fields = Fields::from_iter(ctx.new_from(), pats);

            DeconstructedPat::new(ctor.clone(), fields, ctx.ty, Span::dummy())
        };

        self.0.push(pat);
        self
    }
}

/// A row of a matrix. Rows of len 1 are very common, which is why `SmallVec[_;
/// 2]` works well.
#[derive(Clone)]
struct PatStack<'p> {
    pats: SmallVec<[&'p DeconstructedPat; 2]>,
}

impl<'gs> PatStack<'gs> {
    /// Construct a [PatStack] with a single pattern.
    fn singleton(pat: &'gs DeconstructedPat) -> Self {
        Self::from_vec(smallvec![pat])
    }

    /// Construct a [PatStack] from a [SmallVec].
    fn from_vec(vec: SmallVec<[&'gs DeconstructedPat; 2]>) -> Self {
        PatStack { pats: vec }
    }

    /// Check whether the current [PatStack] is empty
    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    /// Get the length of the [PatStack]
    fn len(&self) -> usize {
        self.pats.len()
    }

    /// Get the head of the current [PatStack]
    fn head(&self) -> &'gs DeconstructedPat {
        self.pats[0]
    }

    /// Iterate over the items within the [PatStack].
    fn iter(&self) -> impl Iterator<Item = &DeconstructedPat> {
        self.pats.iter().copied()
    }

    /// Recursively expand the first pattern into its sub-patterns. Only useful
    /// if the pattern is an or-pattern.
    ///
    /// Panics if `self` is empty.
    fn expand_or_pat<'a>(&'a self, ctx: StorageRefMut<'gs, '_, '_, '_>) -> impl Iterator<Item = PatStack<'gs>> + 'a {
        self.head().iter_fields(ctx).map(move |pat| {
            let mut new_stack = PatStack::singleton(pat);
            new_stack.pats.extend_from_slice(&self.pats[1..]);
            new_stack
        })
    }

    /// This computes `S(self.head().ctor(), self)`. See top of the file for
    /// explanations.
    ///
    ///
    /// @@Todo: Structure patterns with a partial wild pattern `Foo(a: 42, ..)`
    /// have their missing fields filled with wild patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    fn pop_head_constructor(
        &self,
        mut ctx: PatCtx<'gs, '_, '_, '_>,
        ctor: &Constructor,
    ) -> PatStack<'gs> {
        // We pop the head pattern and push the new fields extracted from the arguments
        // of `self.head()`.
        let mut new_fields: SmallVec<[_; 2]> = self.head().specialise(ctx.new_from(), ctor);
        new_fields.extend_from_slice(&self.pats[1..]);

        PatStack::from_vec(new_fields)
    }
}

/// A 2D matrix.
#[derive(Clone)]
pub(super) struct Matrix<'p> {
    patterns: Vec<PatStack<'p>>,
}

impl<'gs> Matrix<'gs> {
    /// Create a new [Matrix] with zero rows and columns.
    fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    /// Number of columns of this matrix. `None` is the matrix is empty.
    pub(super) fn column_count(&self) -> Option<usize> {
        self.patterns.get(0).map(|r| r.len())
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern,
    /// this recursively expands it.
    fn push(&mut self, ctx: StorageRefMut<'gs, '_, '_, '_>, row: PatStack<'gs>) {
        if !row.is_empty() && row.head().is_or_pat() {
            self.patterns.extend(row.expand_or_pat(ctx));
        } else {
            self.patterns.push(row);
        }
    }

    /// Iterate over the first component of each row
    fn heads<'a>(&'a self) -> impl Iterator<Item = &'gs DeconstructedPat> + Clone + 'a {
        self.patterns.iter().map(|r| r.head())
    }

    /// This computes `S(constructor, self)`. See top of the file for
    /// explanations.
    fn specialize_constructor(
        &self,
        mut ctx: PatCtx<'gs, '_, '_, '_>,
        ctor: &Constructor,
    ) -> Matrix<'gs> {
        let mut matrix = Matrix::empty();

        for row in &self.patterns {
            if ctor.is_covered_by(ctx.new_from(), row.head().ctor()) {
                let new_row = row.pop_head_constructor(ctx.new_from(), ctor);
                matrix.push(ctx.storages_mut(), new_row);
            }
        }
        matrix
    }
}

/// Pretty-printer for matrices of patterns, example:
///
/// ```text
/// | _     | []                |
/// | true  | [First]           |
/// | true  | [Second(true)]    |
/// | false | [_]               |
/// | _     | [_, _, ...tail]   |
/// ```
impl<'p> fmt::Debug for Matrix<'p> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;

        let Matrix { patterns: m, .. } = self;
        let pretty_printed_matrix: Vec<Vec<String>> =
            m.iter().map(|row| row.iter().map(|pat| format!("{:?}", pat)).collect()).collect();

        let column_count = m.iter().map(|row| row.len()).next().unwrap_or(0);
        assert!(m.iter().all(|row| row.len() == column_count));
        let column_widths: Vec<usize> = (0..column_count)
            .map(|col| pretty_printed_matrix.iter().map(|row| row[col].len()).max().unwrap_or(0))
            .collect();

        for row in pretty_printed_matrix {
            write!(f, "|")?;
            for (column, pat_str) in row.into_iter().enumerate() {
                write!(f, " ")?;
                write!(f, "{:1$}", pat_str, column_widths[column])?;
                write!(f, " +")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
enum Usefulness {
    /// If we don't care about witnesses, simply remember if the pattern was
    /// useful.
    NoWitnesses { useful: bool },
    /// Carries a list of witnesses of non-exhaustiveness. If empty, indicates
    /// that the whole pattern is unreachable.
    WithWitnesses(Vec<Witness>),
}

impl<'gs, 'ls, 'cd, 's> Usefulness {
    /// Create a `useful` [Usefulness] report.
    fn new_useful(preference: MatchArmKind) -> Self {
        match preference {
            // A single (empty) witness of reachability.
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: true },
        }
    }

    /// Create a `useless` [Usefulness] report.
    fn new_not_useful(preference: MatchArmKind) -> Self {
        match preference {
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: false },
        }
    }

    /// Check if the [Usefulness] report specifies that the pattern is useful.
    fn is_useful(&self) -> bool {
        match self {
            Usefulness::NoWitnesses { useful } => *useful,
            Usefulness::WithWitnesses(witnesses) => !witnesses.is_empty(),
        }
    }

    /// Combine usefulnesses from two branches. This is an associative
    /// operation.
    fn extend(&mut self, other: Self) {
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

    /// After calculating usefulness after a specialization, call this to
    /// reconstruct a usefulness that makes sense for the matrix
    /// pre-specialization. This new usefulness can then be merged
    /// with the results of specializing with the other constructors.
    fn apply_constructor(
        self,
        mut ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        matrix: &Matrix<'gs>, // used to compute missing ctors
        ctor: &Constructor,
    ) -> Self {
        match self {
            Usefulness::NoWitnesses { .. } => self,
            Usefulness::WithWitnesses(ref witnesses) if witnesses.is_empty() => self,
            Usefulness::WithWitnesses(witnesses) => {
                let new_witnesses = if let Constructor::Missing = ctor {
                    // We got the special `Missing` constructor, so each of the
                    // missing constructors gives a new
                    // pattern that is not caught by the match. We list those
                    // patterns.
                    let mut split_wildcard = SplitWildcard::new(ctx.new_from());
                    split_wildcard
                        .split(ctx.new_from(), matrix.heads().map(DeconstructedPat::ctor));

                    // Get all the missing constructors for the current type
                    let missing_ctors = split_wildcard.iter_missing(ctx.new_from()).collect_vec();

                    let new_pats = missing_ctors
                        .into_iter()
                        .map(|missing_ctor| {
                            DeconstructedPat::wild_from_ctor(ctx.new_from(), missing_ctor.clone())
                        })
                        .collect_vec();

                    witnesses
                        .into_iter()
                        .flat_map(|witness| {
                            new_pats.iter().map(move |pat| {
                                Witness(
                                    witness
                                        .0
                                        .iter()
                                        .chain(once(pat))
                                        .map(DeconstructedPat::clone_and_forget_reachability)
                                        .collect(),
                                )
                            })
                        })
                        .collect()
                } else {
                    witnesses
                        .into_iter()
                        .map(|witness| witness.apply_constructor(ctx.new_from(), ctor))
                        .collect()
                };

                Usefulness::WithWitnesses(new_witnesses)
            }
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
/// This finds whether a (row) vector `v` of patterns is 'useful' in relation
/// to a set of such vectors `m` - this is defined as there being a set of
/// inputs that will match `v` but not any of the sets in `m`.
///
/// All the patterns at each column of the `matrix ++ v` matrix must have the
/// same type.
///
/// This is used both for reachability checking (if a pattern isn't useful in
/// relation to preceding patterns, it is not reachable) and exhaustiveness
/// checking (if a wildcard pattern is useful in relation to a matrix, the
/// matrix isn't exhaustive).
///
/// `is_under_guard` is used to inform if the pattern has a guard. If it
/// has one it must not be inserted into the matrix. This shouldn't be
/// relied on for soundness.
fn is_useful<'gs, 'ls, 'cd, 's>(
    mut storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
    matrix: &Matrix<'gs>,
    v: &PatStack<'gs>,
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

    let ty = v.head().ty();
    let span = v.head().span();

    // Create a new `PatCtx`, based on on the provided parameters
    let mut ctx = PatCtx::new(storage.storages_mut(), ty, span, is_top_level);
    let mut report = Usefulness::new_not_useful(arm_kind);

    // If the first pattern is an or-pattern, expand it.
    if v.head().is_or_pat() {
        // We try each or-pattern branch in turn.
        let mut matrix = matrix.clone();

        for v in v.expand_or_pat(storage.storages_mut()) {
            let usefulness = ensure_sufficient_stack(|| {
                is_useful(storage.storages_mut(), &matrix, &v, arm_kind, is_under_guard, false)
            });

            report.extend(usefulness);

            // @@Todo: deal with `if-guards` on the patterns themselves.
            //
            // If the pattern has a guard don't add it to the matrix, but otherwise
            // just push it into the matrix, it doesn't matter if it has already
            // been seen in the current `or` pattern since we want to detect
            // redundant members within the or pattern as well... for example:
            //
            // ``` Ok(_) | Ok(3) => ...; ```
            //
            if !is_under_guard {
                matrix.push(storage.storages_mut(), v);
            }
        }
    } else {
        let v_ctor = v.head().ctor();

        // @@Todo: we should check that int ranges don't overlap here, in case
        // they're partially covered by other ranges.

        // We split the head constructor of `v`.
        let split_ctors = v_ctor.split(ctx.new_from(), matrix.heads().map(DeconstructedPat::ctor));
        let start_matrix = &matrix;

        // For each constructor, we compute whether there's a value that starts with it
        // that would witness the usefulness of `v`.
        for ctor in split_ctors {
            // cache the result of `Fields::wildcards` because it is used a lot.
            let spec_matrix = start_matrix.specialize_constructor(ctx.new_from(), &ctor);
            let v = v.pop_head_constructor(ctx.new_from(), &ctor);

            let usefulness = ensure_sufficient_stack(|| {
                is_useful(
                    ctx.new_from().storages_mut(),
                    &spec_matrix,
                    &v,
                    arm_kind,
                    is_under_guard,
                    false,
                )
            });

            let usefulness = usefulness.apply_constructor(ctx.new_from(), start_matrix, &ctor);
            report.extend(usefulness);
        }
    }

    if report.is_useful() {
        v.head().set_reachable();
    }

    report
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
pub(crate) struct MatchArm<'p> {
    /// The pattern must have been lowered through
    /// `check_match::MatchVisitor::lower_pattern`.
    pub(crate) pat: &'p DeconstructedPat,
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
pub(crate) struct UsefulnessReport<'p> {
    /// For each arm of the input, whether that arm is reachable after the arms
    /// above it.
    pub(crate) arm_usefulness: Vec<(MatchArm<'p>, Reachability)>,
    /// If the match is exhaustive, this is empty. If not, this contains
    /// witnesses for the lack of exhaustiveness.
    pub(crate) non_exhaustiveness_witnesses: Vec<DeconstructedPat>,
}

pub(crate) fn compute_match_usefulness<'gs, 'ls, 'cd, 's>(
    mut storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
    _subject: TermId,
    arms: &[MatchArm<'gs>],
) -> UsefulnessReport<'gs> {
    let mut matrix = Matrix::empty();

    // Compute usefulness for each arm in the match
    let arm_usefulness: Vec<_> = arms
        .iter()
        .copied()
        .map(|arm| {
            let v = PatStack::singleton(arm.pat);
            is_useful(storage.storages_mut(), &matrix, &v, MatchArmKind::Real, arm.has_guard, true);

            // We still compute the usefulness of if-guard patterns, but we don't
            // add them into the matrix since we can't guarantee that they
            // yield all possible conditions
            if !arm.has_guard {
                matrix.push(storage.storages_mut(), v);
            }

            let reachability = if arm.pat.is_reachable() {
                Reachability::Reachable(arm.pat.unreachable_spans(storage.storages_mut()))
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
    let usefulness = is_useful(storage.storages_mut(), &matrix, &v, MatchArmKind::ExhaustiveWildcard, false, true);

    // It should not be possible to not get any witnesses since we're matching
    // on a wildcard, the base case is that `pats` is empty and thus the
    // set of patterns that are provided in the match block are exhaustive.
    let non_exhaustiveness_witnesses = match usefulness {
        Usefulness::WithWitnesses(pats) => pats.into_iter().map(|w| w.single_pattern()).collect(),
        Usefulness::NoWitnesses { .. } => panic!(),
    };

    UsefulnessReport { arm_usefulness, non_exhaustiveness_witnesses }
}
