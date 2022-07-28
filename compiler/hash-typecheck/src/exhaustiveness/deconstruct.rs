//! This file contains the logic and the intermediate representation for the
//! deconstruction of patterns. Within [crate::exhaustiveness] there is a
//! defined pattern representation [crate::exhaustiveness::Pat], this  
//! file contains the [Constructor] and [DeconstructedPat] representations
//! that are further reduced representations of the patterns in
//! order to reduce the complexity of the usefulness/exhaustiveness
//! algorithms.
#![allow(unused)]

use std::{
    cell::Cell,
    cmp::{max, min},
    fmt, iter,
    ops::RangeInclusive,
};

use hash_source::{
    location::{Span, DUMMY_SPAN},
    string::Str,
};
use smallvec::{smallvec, SmallVec};

use crate::{
    ops::AccessToOps,
    storage::{primitives::TermId, AccessToStorage, StorageRef},
};

use super::{Pat, RangeEnd};

#[derive(Clone, Copy)]
pub struct PatCtx<'gs, 'ls, 'cd, 's> {
    /// Reference to the typechecker storage
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
    /// The term of the current column that is under investigation
    pub ty: TermId,
    /// Span of the current pattern under investigation.
    pub(super) span: Span,
    /// Whether the current pattern is the whole pattern as found in a match
    /// arm, or if it's a sub-pattern.
    pub(super) is_top_level: bool,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for PatCtx<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

#[derive(Clone)]

pub struct IntRange {
    range: RangeInclusive<u128>,

    /// Keeps the bias used for encoding the range. It depends on the type of
    /// the range and possibly the pointer size of the current architecture.
    /// The algorithm ensures we never compare `IntRange`s with different
    /// types/architectures.
    bias: u128,
}

impl IntRange {
    /// Get the boundaries of the current [IntRange]
    pub fn boundaries(&self) -> (u128, u128) {
        (*self.range.start(), *self.range.end())
    }

    /// Check whether `self` is covered by the other range, in other words
    /// if other is a super-range of `self`.
    fn is_subrange(&self, other: &Self) -> bool {
        other.range.start() <= self.range.start() && self.range.end() <= other.range.end()
    }

    /// Get the intersection between `self` and `other` [IntRange]s.
    fn intersection(&self, other: &Self) -> Option<Self> {
        let (lo, hi) = self.boundaries();
        let (other_lo, other_hi) = other.boundaries();

        if lo <= other_hi && other_lo <= hi {
            Some(IntRange { range: max(lo, other_lo)..=min(hi, other_hi), bias: self.bias })
        } else {
            None
        }
    }

    /// See [`Constructor::is_covered_by`] //@@Todo:docs!
    fn is_covered_by(&self, other: &Self) -> bool {
        if self.intersection(other).is_some() {
            // Constructor splitting should ensure that all intersections we encounter are
            // actually inclusions.
            assert!(self.is_subrange(other));
            true
        } else {
            false
        }
    }
}
impl fmt::Debug for IntRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (lo, hi) = self.boundaries();
        let bias = self.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        write!(f, "{}", lo)?;
        write!(f, "{}", RangeEnd::Included)?;
        write!(f, "{}", hi)
    }
}

/// Represents a border between 2 integers. Because the intervals spanning
/// borders must be able to cover every integer, we need to be able to represent
/// 2^128 + 1 such borders.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum IntBorder {
    JustBefore(u128),
    AfterMax,
}

/// A range of integers that is partitioned into disjoint subranges. This does
/// constructor splitting for integer ranges as explained at the top of the
/// file.
///
/// This is fed multiple ranges, and returns an output that covers the input,
/// but is split so that the only intersections between an output range and a
/// seen range are inclusions. No output range straddles the boundary of one of
/// the inputs.
///
/// The following input:
/// ```text
///   |-------------------------| // `self`
/// |------|  |----------|   |----|
///    |-------| |-------|
/// ```
/// would be iterated over as follows:
/// ```text
///   ||---|--||-|---|---|---|--|
/// ```
#[derive(Debug, Clone)]
struct SplitIntRange {
    /// The range we are splitting
    range: IntRange,
    /// The borders of ranges we have seen. They are all contained within
    /// `range`. This is kept sorted.
    borders: Vec<IntBorder>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ListKind {
    Fixed(usize),
    Var(usize, usize),
}

impl ListKind {
    /// Get the arity of the list, based on the kind. For
    /// [ListKind::Var], the `...` is treated as a single wild
    /// card and ignored for this purpose.
    fn arity(self) -> usize {
        match self {
            ListKind::Fixed(length) => length,
            ListKind::Var(prefix, suffix) => prefix + suffix,
        }
    }

    /// Whether this pattern includes patterns of length `other_len`.
    fn covers_length(self, other_len: usize) -> bool {
        match self {
            ListKind::Fixed(len) => len == other_len,
            ListKind::Var(prefix, suffix) => prefix + suffix <= other_len,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) struct List {
    /// `None` if the matched value is a slice, `Some(n)` if it is an array of
    /// size `n`.
    array_len: Option<usize>,
    /// The kind of pattern it is: fixed-length `[x, y]` or variable length `[x,
    /// ..., y]`.
    kind: ListKind,
}

impl List {
    fn new(array_len: Option<usize>, kind: ListKind) -> Self {
        let kind = match (array_len, kind) {
            // If the middle `...` is empty, we effectively have a fixed-length pattern.
            (Some(len), ListKind::Var(prefix, suffix)) if prefix + suffix >= len => {
                ListKind::Fixed(len)
            }
            _ => kind,
        };
        List { array_len, kind }
    }

    fn arity(self) -> usize {
        self.kind.arity()
    }

    fn is_covered_by(self, other: Self) -> bool {
        other.kind.covers_length(self.arity())
    }
}

#[derive(Debug)]
struct SplitVarLenSlice {
    /// If the type is an array, this is its size.
    array_len: Option<usize>,
    /// The arity of the input slice.
    arity: usize,
    /// The smallest slice bigger than any slice seen. `max_slice.arity()` is
    /// the length `L` described above.
    max_slice: ListKind,
}

impl SplitVarLenSlice {
    fn new(prefix: usize, suffix: usize, array_len: Option<usize>) -> Self {
        SplitVarLenSlice {
            array_len,
            arity: prefix + suffix,
            max_slice: ListKind::Var(prefix, suffix),
        }
    }

    /// Pass a set of slices relative to which to split this one.
    fn split(&mut self, slices: impl Iterator<Item = ListKind>) {}

    /// Iterate over the partition of this slice.
    fn iter<'a>(&'a self) -> impl Iterator<Item = List> + 'a {
        let smaller_lengths = match self.array_len {
            // The only admissible fixed-length slice is one of the array size. Whether `max_slice`
            // is fixed-length or variable-length, it will be the only relevant slice to output
            // here.
            Some(_) => (0..0), // empty range
            // We cover all arities in the range `(self.arity..infinity)`. We split that range into
            // two: lengths smaller than `max_slice.arity()` are treated independently as
            // fixed-lengths slices, and lengths above are captured by `max_slice`.
            None => self.arity..self.max_slice.arity(),
        };

        smaller_lengths
            .map(ListKind::Fixed)
            .chain(iter::once(self.max_slice))
            .map(move |kind| List::new(self.array_len, kind))
    }
}

#[derive(Debug)]
pub(super) struct SplitWildcard {
    /// Constructors seen in the matrix.
    matrix_ctors: Vec<Constructor>,
    /// All the constructors for this type
    all_ctors: SmallVec<[Constructor; 1]>,
}

impl<'gs, 'ls, 'cd, 's> SplitWildcard {
    pub(super) fn new(ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> Self {
        let reader = ctx.reader();

        let all_ctors = match reader.get_term(ctx.ty) {
            // @@Todo: we should just default to having a `non-exhaustive` variant within the
            // constructors
            _ => smallvec![],
        };

        SplitWildcard { matrix_ctors: Vec::new(), all_ctors }
    }
}

/// The [Constructor] represents the type of constructor that a pattern
/// is.
///
/// @@Todo: float and integer ranges
#[derive(Debug, Clone)]
pub(super) enum Constructor {
    /// The constructor for patterns that have a single constructor, like
    /// tuples, struct patterns and fixed-length arrays.
    Single,
    /// Enum variants.
    Variant(usize),
    /// Ranges of integer literal values (`2`, `2..=5` or `2..5`).
    IntRange(IntRange),
    /// String literals.
    Str(Str),
    /// List patterns
    List(List),
    /// Wildcard pattern.
    Wildcard,
    /// Or-pattern.
    Or,
    /// Stands for constructors that are not seen in the matrix, as explained in
    /// the documentation for [`SplitWildcard`].
    Missing,
}

impl Constructor {
    /// Compute the `arity` of this [Constructor].
    pub fn arity(&self) -> usize {
        match self {
            Constructor::Single | Constructor::Variant(_) => {
                // we need to get term from the context here...
                //
                // if it a tuple, get the length and that is the arity
                // if it is a struct or enum, then we get that variant and
                // we can count the fields from that variant or struct.

                todo!()
            }
            Constructor::List(list) => list.arity(),
            Constructor::IntRange(_)
            | Constructor::Str(_)
            | Constructor::Wildcard
            | Constructor::Missing => 0,
            Constructor::Or => panic!("`Or` constructor doesn't have a fixed arity"),
        }
    }

    /// Try and convert the [Constructor] into a [IntRange].
    fn as_int_range(&self) -> Option<&IntRange> {
        match self {
            Constructor::IntRange(range) => Some(range),
            _ => None,
        }
    }

    /// Try and convert the [Constructor] into a [List].
    fn as_list(&self) -> Option<&List> {
        match self {
            Constructor::List(list) => Some(list),
            _ => None,
        }
    }

    pub(super) fn split<'a>(
        &self,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) -> SmallVec<[Self; 1]> {
        todo!()
    }

    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a
    /// subset of `other`. For the simple cases, this is simply checking for
    /// equality. For the "grouped" constructors, this checks for inclusion.
    #[inline]
    pub(super) fn is_covered_by<'p>(&self, other: &Self) -> bool {
        match (self, other) {
            // Wildcards cover anything
            (_, Constructor::Wildcard) => true,
            // The missing ctors are not covered by anything in the matrix except wildcards.
            (Constructor::Missing | Constructor::Wildcard, _) => false,

            (Constructor::Single, Constructor::Single) => true,
            (Constructor::Variant(self_id), Constructor::Variant(other_id)) => self_id == other_id,

            (Constructor::IntRange(self_range), Constructor::IntRange(other_range)) => {
                self_range.is_covered_by(other_range)
            }

            // It's safe to compare the `id`s of the allocated strings since they are
            // de-duplicated.
            (Constructor::Str(self_str), Constructor::Str(other_str)) => self_str == other_str,

            (Constructor::List(self_slice), Constructor::List(other_slice)) => {
                self_slice.is_covered_by(*other_slice)
            }

            // @@Todo: use `panic_on_span`
            _ => panic!("trying to compare incompatible constructors {:?} and {:?}", self, other),
        }
    }

    /// Faster version of `is_covered_by` when applied to many constructors.
    /// `used_ctors` is assumed to be built from `matrix.head_ctors()` with
    /// wildcards filtered out, and `self` is assumed to have been split
    /// from a wildcard.
    fn is_covered_by_any(&self, used_ctors: &[Constructor]) -> bool {
        if used_ctors.is_empty() {
            return false;
        }

        match self {
            // If `self` is `Single`, `used_ctors` cannot contain anything else than `Single`s.
            Constructor::Single => !used_ctors.is_empty(),
            Constructor::Variant(i) => {
                used_ctors.iter().any(|c| matches!(c, Constructor::Variant(k) if k == i))
            }
            Constructor::IntRange(range) => used_ctors
                .iter()
                .filter_map(|c| c.as_int_range())
                .any(|other| range.is_covered_by(other)),
            Constructor::List(list) => used_ctors
                .iter()
                .filter_map(|c| c.as_list())
                .any(|other| list.is_covered_by(*other)),
            Constructor::Str(_)
            | Constructor::Missing
            | Constructor::Wildcard
            | Constructor::Or => {
                // @@TODO: integrate `PatCtx` here...
                panic!("Unexpected ctor in all_ctors")
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Fields<'p> {
    fields: &'p [DeconstructedPat<'p>],
}

impl<'p> Fields<'p> {
    fn empty() -> Self {
        Fields { fields: &[] }
    }

    /// Returns the list of patterns.
    pub(super) fn iter_patterns<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> {
        self.fields.iter()
    }

    pub(super) fn from_iter(
        // cx: &MatchCheckCtxt<'p, 'tcx>,
        fields: impl IntoIterator<Item = DeconstructedPat<'p>>,
    ) -> Self {
        // let fields: &[_] = cx.pattern_arena.alloc_from_iter(fields);
        // Fields { fields }
        todo!()
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result must have a length of `ctor.arity()`.
    pub(super) fn wildcards(
        // cx: &MatchCheckCtxt<'p, 'tcx>,
        ctor: &Constructor,
    ) -> Self {
        todo!()
    }
}

/// A [DeconstructedPat] is a representation of a [Constructor] that is split
/// between the constructor subject `ctor` and the `fields` that the constructor
/// hilds.
///
/// @@Todo: Implement `fmt` for the deconstructed pat as this is what will be
/// used         for displaying these patterns.
#[derive(Debug)]
pub(crate) struct DeconstructedPat<'p> {
    /// The subject of the [DeconstructedPat].
    ctor: Constructor,
    /// Any fields that are applying to the subject of the
    /// [DeconstructedPat]
    fields: Fields<'p>,
    /// The [Span] of the current pattern.
    span: Span,
    /// Whether the current pattern is reachable.
    reachable: Cell<bool>,
}

impl<'p, 'gs, 'ls, 'cd, 's> DeconstructedPat<'p> {
    pub(super) fn new(ctor: Constructor, fields: Fields<'p>, span: Span) -> Self {
        DeconstructedPat { ctor, fields, span, reachable: Cell::new(false) }
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard() -> Self {
        Self::new(Constructor::Wildcard, Fields::empty(), DUMMY_SPAN)
    }

    pub(super) fn wild_from_ctor(
        // pcx: PatCtxt<'_, 'p, 'tcx>,
        ctor: Constructor,
    ) -> Self {
        let fields = Fields::wildcards(&ctor);

        DeconstructedPat::new(ctor, fields, DUMMY_SPAN)
    }

    /// Clone this [DeconstructedPat] whilst also forgetting the reachability.
    pub(super) fn clone_and_forget_reachability(&self) -> Self {
        DeconstructedPat::new(self.ctor.clone(), self.fields, self.span)
    }

    pub(crate) fn from_pat(pat: &Pat) -> Self {
        todo!()
    }

    pub(crate) fn to_pat(&self) -> Pat {
        todo!()
    }

    pub(super) fn is_or_pat(&self) -> bool {
        matches!(self.ctor, Constructor::Or)
    }

    pub(super) fn ctor(&self) -> &Constructor {
        &self.ctor
    }

    pub(super) fn span(&self) -> Span {
        self.span
    }

    pub(super) fn iter_fields<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> {
        self.fields.iter_patterns()
    }

    pub(super) fn specialise<'a>(
        &'a self,
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        other_ctor: &Constructor,
    ) -> SmallVec<[&'p DeconstructedPat<'p>; 2]> {
        match (&self.ctor, other_ctor) {
            (Constructor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                Fields::wildcards(other_ctor).iter_patterns().collect()
            }
            (Constructor::List(self_list), Constructor::List(other_list))
                if self_list.arity() != other_list.arity() =>
            {
                // If the arities mismatch, `self_list` must cover `other_list` and thus
                // it must be that `other_list` is a variable length list. Then, `other_list`
                // will have a guaranteed larger arity that `self_list`.
                //
                // So when specialising, we will fill the middle part of the `self_list` to
                // match the arity of the `other_list`.
                match self_list.kind {
                    ListKind::Fixed(_) => panic!("{:?} cannot cover {:?}", self_list, other_list),
                    ListKind::Var(prefix, suffix) => {
                        // @@Todo: we will need to get the inner `ty` of the list

                        let prefix = &self.fields.fields[..prefix];
                        let suffix = &self.fields.fields[self_list.arity() - suffix..];

                        todo!()
                        // let wildcard: &_ = &DeconstructedPat::wildcard();

                        // let extra_wildcards = other_list.arity() -
                        // self_list.arity();
                        // let extra_wildcards = (0..extra_wildcards).map(|_|
                        // wildcard); prefix.iter().
                        // chain(extra_wildcards).chain(suffix).collect()
                    }
                }
            }
            _ => self.fields.iter_patterns().collect(),
        }
    }

    /// We keep track for each pattern if it was ever reachable during the
    /// analysis. This is used with `unreachable_spans` to report
    /// unreachable sub-patterns arising from or patterns.
    pub(super) fn set_reachable(&self) {
        self.reachable.set(true)
    }
    pub(super) fn is_reachable(&self) -> bool {
        self.reachable.get()
    }

    /// Report the spans of sub-patterns that were not reachable, if any.
    pub(super) fn unreachable_spans(&self) -> Vec<Span> {
        let mut spans = Vec::new();
        self.collect_unreachable_spans(&mut spans);
        spans
    }

    fn collect_unreachable_spans(&self, spans: &mut Vec<Span>) {
        // We don't look at sub-patterns if we already reported the whole pattern as
        // unreachable.
        if !self.is_reachable() {
            spans.push(self.span);
        } else {
            for p in self.iter_fields() {
                p.collect_unreachable_spans(spans);
            }
        }
    }
}
