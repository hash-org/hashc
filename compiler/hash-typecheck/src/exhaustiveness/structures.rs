use super::{fields::Fields, Pat, PatKind};
use crate::storage::primitives::TermId;
use hash_source::{location::Span, string::Str};
use smallvec::SmallVec;
use std::{
    cell::Cell,
    cmp::{max, min},
    fmt::{self, Display},
    iter::once,
    ops::RangeInclusive,
};

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum RangeEnd {
    Included,
    Excluded,
}

impl Display for RangeEnd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RangeEnd::Included => write!(f, "..="),
            RangeEnd::Excluded => write!(f, ".."),
        }
    }
}

#[derive(Copy, Clone)]
pub struct PatCtx {
    /// Reference to the typechecker storage
    // pub storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
    /// The term of the current column that is under investigation
    pub ty: TermId,
    /// Span of the current pattern under investigation.
    pub(super) span: Span,
    /// Whether the current pattern is the whole pattern as found in a match
    /// arm, or if it's a sub-pattern.
    pub(super) is_top_level: bool,
}

impl PatCtx {
    /// Create a new [PatCtx]
    pub fn new(ty: TermId, span: Span, is_top_level: bool) -> Self {
        PatCtx { ty, span, is_top_level }
    }
}

#[derive(Clone)]

pub struct IntRange {
    pub range: RangeInclusive<u128>,

    /// Keeps the bias used for encoding the range. It depends on the type of
    /// the range and possibly the pointer size of the current architecture.
    /// The algorithm ensures we never compare `IntRange`s with different
    /// types/architectures.
    pub bias: u128,
}

impl IntRange {
    /// Get the boundaries of the current [IntRange]
    pub fn boundaries(&self) -> (u128, u128) {
        (*self.range.start(), *self.range.end())
    }

    /// Check whether `self` is covered by the other range, in other words
    /// if other is a super-range of `self`.
    pub fn is_subrange(&self, other: &Self) -> bool {
        other.range.start() <= self.range.start() && self.range.end() <= other.range.end()
    }

    /// Get the intersection between `self` and `other` [IntRange]s.
    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let (lo, hi) = self.boundaries();
        let (other_lo, other_hi) = other.boundaries();

        if lo <= other_hi && other_lo <= hi {
            Some(IntRange { range: max(lo, other_lo)..=min(hi, other_hi), bias: self.bias })
        } else {
            None
        }
    }

    /// Check whether the [IntRange] is a singleton, or in other words if there
    /// is only one step within the range
    pub fn is_singleton(&self) -> bool {
        self.range.start() == self.range.end()
    }

    /// See [`Constructor::is_covered_by`] //@@Todo:docs!
    pub fn is_covered_by(&self, other: &Self) -> bool {
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
pub enum IntBorder {
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
pub struct SplitIntRange {
    /// The range we are splitting
    range: IntRange,
    /// The borders of ranges we have seen. They are all contained within
    /// `range`. This is kept sorted.
    borders: Vec<IntBorder>,
}

impl SplitIntRange {
    /// Create a new [SplitIntRange]
    pub fn new(range: IntRange) -> Self {
        SplitIntRange { range, borders: Vec::new() }
    }

    /// Convert the [SplitIntRange] into its respective borders.
    pub fn to_borders(r: IntRange) -> (IntBorder, IntBorder) {
        let (lo, hi) = r.boundaries();
        let lo = IntBorder::JustBefore(lo);

        let hi = match hi.checked_add(1) {
            Some(m) => IntBorder::JustBefore(m),
            None => IntBorder::AfterMax,
        };

        (lo, hi)
    }

    /// Add ranges relative to which we split.
    pub fn split(&mut self, ranges: impl Iterator<Item = IntRange>) {
        let this_range = &self.range;
        let included_ranges = ranges.filter_map(|r| this_range.intersection(&r));
        let included_borders = included_ranges.flat_map(|r| {
            let (lo, hi) = Self::to_borders(r);
            once(lo).chain(once(hi))
        });

        self.borders.extend(included_borders);
        self.borders.sort_unstable();
    }

    /// Iterate over the contained ranges.
    pub fn iter(&self) -> impl Iterator<Item = IntRange> + '_ {
        let (lo, hi) = Self::to_borders(self.range.clone());
        // Start with the start of the range.
        let mut prev_border = lo;

        self.borders
            .iter()
            .copied()
            // End with the end of the range.
            .chain(once(hi))
            // List pairs of adjacent borders.
            .map(move |border| {
                let ret = (prev_border, border);
                prev_border = border;
                ret
            })
            // Skip duplicates.
            .filter(|(prev_border, border)| prev_border != border)
            // Finally, convert to ranges.
            .map(move |(prev_border, border)| {
                let range = match (prev_border, border) {
                    (IntBorder::JustBefore(n), IntBorder::JustBefore(m)) if n < m => n..=(m - 1),
                    (IntBorder::JustBefore(n), IntBorder::AfterMax) => n..=u128::MAX,
                    _ => unreachable!(), // Ruled out by the sorting and filtering we did
                };
                IntRange { range, bias: self.range.bias }
            })
    }
}

/// Represents the kind of [List], whether it is
/// of a fixed length or of a variable length.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ListKind {
    /// When the size of the list pattern is known.
    Fixed(usize),
    /// When the list pattern features a spread pattern, the
    /// first number is the length of the prefix elements, and
    /// the succeeding number is the length of the suffix
    /// elements.
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
pub struct List {
    /// The kind of pattern it is: fixed-length `[x, y]` or
    /// variable length `[x, ..., y]`.
    pub kind: ListKind,
}

impl List {
    /// Construct a new [List] with a provided kind.
    pub(crate) fn new(kind: ListKind) -> Self {
        Self { kind }
    }

    /// Compute the arity of the [List]
    pub(crate) fn arity(self) -> usize {
        self.kind.arity()
    }

    /// Whether another [List] would cover this [List].
    pub(crate) fn is_covered_by(self, other: Self) -> bool {
        other.kind.covers_length(self.arity())
    }
}

#[derive(Debug)]
pub struct SplitVarList {
    /// The arity of the input slice.
    arity: usize,
    /// The smallest list bigger than any list seen. `max_list.arity()` is
    /// the length `L` described above.
    max_list: ListKind,
}

impl SplitVarList {
    pub fn new(prefix: usize, suffix: usize) -> Self {
        SplitVarList { arity: prefix + suffix, max_list: ListKind::Var(prefix, suffix) }
    }

    /// Pass a set of slices relative to which to split this one.
    ///
    /// We don't need to split the [List] if the kind is [ListKind::Fixed].
    pub fn split(&mut self, slices: impl Iterator<Item = ListKind>) {
        let ListKind::Var(max_prefix_len, max_suffix_len) = &mut self.max_list else {
            return;
        };

        // We grow `self.max_list` to be larger than all slices encountered, as
        // described above. For diagnostics, we keep the prefix and suffix
        // lengths separate, but grow them so that `L = max_prefix_len +
        // max_suffix_len`.
        let mut max_fixed_len = 0;

        for slice in slices {
            match slice {
                ListKind::Fixed(len) => {
                    max_fixed_len = max(max_fixed_len, len);
                }
                ListKind::Var(prefix, suffix) => {
                    *max_prefix_len = max(*max_prefix_len, prefix);
                    *max_suffix_len = max(*max_suffix_len, suffix);
                }
            }
        }

        // We want `L = max(L, max_fixed_len + 1)`, modulo the fact that we keep prefix
        // and suffix separate.
        //
        // This ensures that the size adjustment of `max_prefix_len` can't overflow
        if max_fixed_len + 1 >= *max_prefix_len + *max_suffix_len {
            *max_prefix_len = max_fixed_len + 1 - *max_suffix_len;
        }
    }

    /// Iterate over the partition of this slice.
    pub fn iter(&self) -> impl Iterator<Item = List> + '_ {
        // We cover all arities in the range `(self.arity..infinity)`. We split that
        // range into two: lengths smaller than `max_slice.arity()` are treated
        // independently as fixed-lengths slices, and lengths above are captured
        // by `max_slice`.
        let smaller_lengths = self.arity..self.max_list.arity();

        smaller_lengths.map(ListKind::Fixed).chain(once(self.max_list)).map(List::new)
    }
}

/// The [Constructor] represents the type of constructor that a pattern
/// is.
///
/// @@Todo: float ranges
#[derive(Debug, Clone)]
pub enum Constructor {
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
    /// Declared as non-exhaustive
    NonExhaustive,
}

impl Constructor {
    /// Check if the [Constructor] is non-exhaustive.
    pub(super) fn is_non_exhaustive(&self) -> bool {
        matches!(self, Constructor::NonExhaustive)
    }

    /// Check if the [Constructor] is a wildcard.
    pub(super) fn is_wildcard(&self) -> bool {
        matches!(self, Constructor::Wildcard)
    }

    /// Try and convert the [Constructor] into a [IntRange].
    pub fn as_int_range(&self) -> Option<&IntRange> {
        match self {
            Constructor::IntRange(range) => Some(range),
            _ => None,
        }
    }

    /// Try and convert the [Constructor] into a [List].
    pub fn as_list(&self) -> Option<&List> {
        match self {
            Constructor::List(list) => Some(list),
            _ => None,
        }
    }
}

/// A [DeconstructedPat] is a representation of a [Constructor] that is split
/// between the constructor subject `ctor` and the `fields` that the constructor
/// holds.
///
/// @@Todo: Implement `fmt` for the deconstructed pat as this is what will be
/// used         for displaying these patterns.
#[derive(Debug, Clone)]
pub struct DeconstructedPat {
    /// The subject of the [DeconstructedPat].
    pub ctor: Constructor,
    /// Any fields that are applying to the subject of the
    /// [DeconstructedPat]
    pub fields: Fields,
    /// The type of the current deconstructed pattern
    pub ty: TermId,
    /// The [Span] of the current pattern.
    pub span: Span,
    /// Whether the current pattern is reachable.
    pub reachable: Cell<bool>,
}

impl DeconstructedPat {
    pub(super) fn new(ctor: Constructor, fields: Fields, ty: TermId, span: Span) -> Self {
        DeconstructedPat { ctor, fields, span, ty, reachable: Cell::new(false) }
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard(ty: TermId) -> Self {
        Self::new(Constructor::Wildcard, Fields::empty(), ty, Span::dummy())
    }

    /// Clone this [DeconstructedPat] whilst also forgetting the reachability.
    pub(super) fn clone_and_forget_reachability(&self) -> Self {
        DeconstructedPat::new(self.ctor.clone(), self.fields.clone(), self.ty, self.span)
    }

    /// Expand an `or` pattern into a passed [Vec], whilst also
    /// applying the same operation on children patterns.
    pub fn expand<'p>(pat: &'p Pat, vec: &mut Vec<&'p Pat>) {
        if let PatKind::Or { pats } = pat.kind.as_ref() {
            for pat in pats {
                Self::expand(pat, vec);
            }
        } else {
            vec.push(pat)
        }
    }

    /// Internal use for expanding an [PatKind::Or] into children
    /// patterns. This will also expand any children that are `or`
    /// patterns.
    pub fn flatten_or_pat<'p>(pat: &'p Pat) -> Vec<&'p Pat> {
        let mut pats = Vec::new();
        Self::expand(pat, &mut pats);
        pats
    }

    pub(super) fn is_or_pat(&self) -> bool {
        matches!(self.ctor, Constructor::Or)
    }

    /// Function to get the constructor of the [DeconstructedPat]
    pub(super) fn ctor(&self) -> &Constructor {
        &self.ctor
    }

    /// Function to get the `span` of the [DeconstructedPat]
    pub(super) fn span(&self) -> Span {
        self.span
    }

    /// Function to get the `ty` of the [DeconstructedPat]
    pub(super) fn ty(&self) -> TermId {
        self.ty
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
}

#[derive(Debug)]
pub struct SplitWildcard {
    /// Constructors seen in the matrix.
    pub matrix_ctors: Vec<Constructor>,
    /// All the constructors for this type
    pub all_ctors: SmallVec<[Constructor; 1]>,
}
