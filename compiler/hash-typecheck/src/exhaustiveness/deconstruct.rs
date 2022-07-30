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
    fmt,
    iter::{self, once},
    ops::RangeInclusive,
};

use hash_reporting::macros::panic_on_span;
use hash_source::{
    location::{SourceLocation, Span, DUMMY_SPAN},
    string::Str,
};
use itertools::Itertools;
use num_bigint::Sign;
use smallvec::{smallvec, SmallVec};

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::PatKind,
    ops::AccessToOps,
    storage::{
        primitives::{
            ConstructedTerm, Level0Term, Level1Term, LitTerm, NominalDef, Term, TermId, TupleLit,
        },
        AccessToStorage, StorageRef,
    },
};

use super::{
    constant::{self, Constant},
    FieldPat, Pat, RangeEnd,
};

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

impl<'gs, 'ls, 'cd, 's> PatCtx<'gs, 'ls, 'cd, 's> {
    /// Get a [SourceLocation] from the current [PatCtx]
    fn location(&self) -> SourceLocation {
        SourceLocation {
            span: self.span,
            source_id: self.storage.checked_sources().current_source(),
        }
    }
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

impl<'gs, 'ls, 'cd, 's> IntRange {
    /// Get the boundaries of the current [IntRange]
    pub fn boundaries(&self) -> (u128, u128) {
        (*self.range.start(), *self.range.end())
    }

    /// Attempt to build a [IntRange] from a provided constant.
    #[inline]
    pub fn from_constant(ctx: PatCtx<'gs, 'ls, 'cd, 's>, constant: Constant) -> Self {
        let reader = ctx.reader();

        let bias: u128 = match reader.get_term(constant.ty) {
            Term::Level0(Level0Term::Lit(lit)) => match lit {
                LitTerm::Int { kind, .. } if kind.is_signed() => {
                    // @@Todo: support `ibig` type here
                    let size = kind.size().unwrap();
                    1u128 << (size * 8 - 1)
                }
                LitTerm::Char(_) | LitTerm::Int { .. } => 0,
                LitTerm::Str(_) => panic!("got `str` in const!"),
            },
            _ => tc_panic!(
                constant.ty,
                ctx,
                "got unexpected ty `{}` when reading Constant.",
                ctx.for_fmt(constant.ty)
            ),
        };

        // read from the constant the actual bits and apply bias
        let val = constant.data() ^ bias;
        IntRange { range: val..=val, bias }
    }

    /// Create an [IntRange] from two specified bounds, and assuming that the
    /// type is an integer (of the column)
    fn from_range(
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        lo: u128,
        hi: u128,
        end: &RangeEnd,
    ) -> IntRange {
        let bias = Self::signed_bias(ctx);

        let (lo, hi) = (lo ^ bias, hi ^ bias);
        let offset = (*end == RangeEnd::Excluded) as u128;
        if lo > hi || (lo == hi && *end == RangeEnd::Excluded) {
            // This should have been caught earlier by E0030.
            panic!("malformed range pattern: {}..={}", lo, (hi - offset));
        }

        IntRange { range: lo..=(hi - offset), bias }
    }

    /// Get the bias based on the type, if it is a signed, integer then
    /// the bias is set to be just at the end of the signed boundary
    /// of the integer size, in other words at the position where the
    /// last byte is that identifies the sign.
    fn signed_bias(ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> u128 {
        let reader = ctx.reader();

        match reader.get_term(ctx.ty) {
            Term::Level0(Level0Term::Lit(LitTerm::Int { kind, .. })) if kind.is_signed() => {
                // @@Future: support `ibig` here
                let size = kind.size().unwrap();
                1u128 << (size * 8 - 1)
            }
            _ => 0,
        }
    }

    /// Whether the type of the column is an integral
    fn is_integral(ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> bool {
        let reader = ctx.reader();

        // @@Incomplete: what about types, not just literal terms
        match reader.get_term(ctx.ty) {
            Term::Level0(Level0Term::Lit(_)) => true,
            _ => false,
        }
    }

    /// Convert this range into a [PatKind] by judging the given
    /// type within the [PatCtx]
    #[inline]
    pub fn to_pat(&self, ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> PatKind {
        let (lo, hi) = self.boundaries();

        let bias = self.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        let lo_const = Constant::from_u128(lo, ctx.ty);
        let hi_const = Constant::from_u128(hi, ctx.ty);

        if lo == hi {
            PatKind::Constant { value: lo_const }
        } else {
            panic!("Ranges are not supported yet")
        }
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

    /// Check whether the [IntRange] is a singleton, or in other words if there
    /// is only one step within the range
    fn is_singleton(&self) -> bool {
        self.range.start() == self.range.end()
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

impl SplitIntRange {
    /// Create a new [SplitIntRange]
    fn new(range: IntRange) -> Self {
        SplitIntRange { range, borders: Vec::new() }
    }

    /// Convert the [SplitIntRange] into its respective borders.
    fn to_borders(r: IntRange) -> (IntBorder, IntBorder) {
        let (lo, hi) = r.boundaries();
        let lo = IntBorder::JustBefore(lo);

        let hi = match hi.checked_add(1) {
            Some(m) => IntBorder::JustBefore(m),
            None => IntBorder::AfterMax,
        };

        (lo, hi)
    }

    /// Add ranges relative to which we split.
    fn split(&mut self, ranges: impl Iterator<Item = IntRange>) {
        let this_range = &self.range;
        let included_ranges = ranges.filter_map(|r| this_range.intersection(&r));
        let included_borders = included_ranges.flat_map(|r| {
            let (lo, hi) = Self::to_borders(r);
            iter::once(lo).chain(iter::once(hi))
        });

        self.borders.extend(included_borders);
        self.borders.sort_unstable();
    }

    /// Iterate over the contained ranges.
    fn iter(&self) -> impl Iterator<Item = IntRange> + '_ {
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
pub(super) struct List {
    /// The kind of pattern it is: fixed-length `[x, y]` or
    /// variable length `[x, ..., y]`.
    kind: ListKind,
}

impl List {
    /// Construct a new [List] with a provided kind.
    fn new(kind: ListKind) -> Self {
        Self { kind }
    }

    /// Compute the arity of the [List]
    fn arity(self) -> usize {
        self.kind.arity()
    }

    /// Whether another [List] would cover this [List].
    fn is_covered_by(self, other: Self) -> bool {
        other.kind.covers_length(self.arity())
    }
}

#[derive(Debug)]
struct SplitVarList {
    /// The arity of the input slice.
    arity: usize,
    /// The smallest list bigger than any list seen. `max_list.arity()` is
    /// the length `L` described above.
    max_list: ListKind,
}

impl SplitVarList {
    fn new(prefix: usize, suffix: usize) -> Self {
        SplitVarList { arity: prefix + suffix, max_list: ListKind::Var(prefix, suffix) }
    }

    /// Pass a set of slices relative to which to split this one.
    ///
    /// We don't need to split the [List] if the kind is [ListKind::Fixed].
    fn split(&mut self, slices: impl Iterator<Item = ListKind>) {
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
    fn iter(&self) -> impl Iterator<Item = List> + '_ {
        // We cover all arities in the range `(self.arity..infinity)`. We split that
        // range into two: lengths smaller than `max_slice.arity()` are treated
        // independently as fixed-lengths slices, and lengths above are captured
        // by `max_slice`.
        let smaller_lengths = self.arity..self.max_list.arity();

        smaller_lengths.map(ListKind::Fixed).chain(iter::once(self.max_list)).map(List::new)
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

        let make_range = |start, end| {
            Constructor::IntRange(IntRange::from_range(ctx, start, end, &RangeEnd::Included))
        };

        // This determines the set of all possible constructors for the type `ctx.ty`.
        // For numbers, lists we use ranges and variable-length lists when appropriate.
        //
        //
        // @@Future:
        // we need make sure to omit constructors that are statically impossible. E.g.,
        // for `Option<!>`, we do not include `Some(_)` in the returned list of
        // constructors.
        let all_ctors = match reader.get_term(ctx.ty) {
            // term if ctx.typer().term_is_char() => ...,
            // term if ctx.typer().term_is_uint() => ...,
            // term if ctx.typer().term_is_int() => ...,
            // term if ctx.typer().term_is_list() => ...,
            Term::Level1(Level1Term::NominalDef(def)) => {
                match reader.get_nominal_def(*def) {
                    NominalDef::Struct(_) => smallvec![Constructor::Single],
                    NominalDef::Enum(enum_def) => {
                        // The exception is if the pattern is at the top level, because we
                        // want empty matches to be
                        // considered exhaustive.
                        let is_secretly_empty = enum_def.variants.is_empty() && !ctx.is_top_level;

                        let mut ctors: SmallVec<[_; 1]> = enum_def
                            .variants
                            .iter()
                            .enumerate()
                            .map(|(index, _)| Constructor::Variant(index))
                            .collect();

                        if is_secretly_empty {
                            ctors.push(Constructor::NonExhaustive);
                        }

                        ctors
                    }
                    _ => smallvec![Constructor::NonExhaustive],
                }
            }
            Term::Level1(Level1Term::Tuple(_)) => smallvec![Constructor::Single],
            _ => smallvec![Constructor::NonExhaustive],
        };

        SplitWildcard { matrix_ctors: Vec::new(), all_ctors }
    }

    pub(super) fn split<'a>(
        &mut self,
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) {
        // Since `all_ctors` never contains wildcards, this won't recurse further.
        self.all_ctors =
            self.all_ctors.iter().flat_map(|ctor| ctor.split(ctx, ctors.clone())).collect();
        self.matrix_ctors = ctors.filter(|c| !c.is_wildcard()).cloned().collect();
    }

    /// Whether there are any value constructors for this type that are not
    /// present in the matrix.
    fn any_missing(&self, ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> bool {
        self.iter_missing(ctx).next().is_some()
    }

    /// Iterate over the constructors for this type that are not present in the
    /// matrix.
    pub(super) fn iter_missing<'a, 'p>(
        &'a self,
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
    ) -> impl Iterator<Item = &'a Constructor> + 'p
    where
        'gs: 'p,
        'ls: 'p,
        'cd: 'p,
        's: 'p,
        'a: 'p,
    {
        self.all_ctors.iter().filter(move |ctor| !ctor.is_covered_by_any(ctx, &self.matrix_ctors))
    }

    fn into_ctors(self, ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> SmallVec<[Constructor; 1]> {
        // If Some constructors are missing, thus we can specialize with the special
        // `Missing` constructor, which stands for those constructors that are
        // not seen in the matrix, and matches the same rows as any of them
        // (namely the wildcard rows). See the top of the file for details.
        if self.any_missing(ctx) {
            // If some constructors are missing, we typically want to report those
            // constructors, e.g.:
            // ```ignore
            //     Direction := enum(N, S, E, W);
            //
            //     dir := Direction::N;
            //     match dir {
            //         Direction::N => ...;
            //     }
            // ```
            // we can report 3 witnesses: `S`, `E`, and `W`.
            //
            // However, if the user didn't actually specify a constructor
            // in this arm, e.g., in
            // ```
            //     x: (Direction, Direction, bool) = ...;
            //     (_, _, false) := x;
            // ```
            // we don't want to show all 16 possible witnesses `(<direction-1>,
            // <direction-2>, true)` - we are satisfied with `(_, _, true)`. So
            // if all constructors are missing we prefer to report just a
            // wildcard `_`.
            //
            // The exception is: if we are at the top-level, for example in an empty match,
            // we sometimes prefer reporting the list of constructors instead of
            // just `_`.
            let ctor = if !self.matrix_ctors.is_empty()
                || (ctx.is_top_level && !IntRange::is_integral(ctx))
            {
                Constructor::Missing
            } else {
                Constructor::Wildcard
            };

            return smallvec![ctor];
        }

        self.all_ctors
    }
}

/// The [Constructor] represents the type of constructor that a pattern
/// is.
///
/// @@Todo: float ranges
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
    /// Declared as non-exhaustive
    NonExhaustive,
}

impl<'gs, 'ls, 'cd, 's> Constructor {
    /// Compute the `arity` of this [Constructor].
    pub fn arity(&self, ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> usize {
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
            | Constructor::NonExhaustive
            | Constructor::Missing => 0,
            Constructor::Or => panic!("`Or` constructor doesn't have a fixed arity"),
        }
    }

    /// Check if the [Constructor] is non-exhaustive.
    pub(super) fn is_non_exhaustive(&self) -> bool {
        matches!(self, Constructor::NonExhaustive)
    }

    /// Check if the [Constructor] is a wildcard.
    pub(super) fn is_wildcard(&self) -> bool {
        matches!(self, Constructor::Wildcard)
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

    /// # Split a [Constructor]
    ///
    /// Some constructors (namely `Wildcard`, `IntRange` and `List`) actually
    /// stand for a set of actual constructors (like variants, integers or
    /// fixed-sized list patterns).
    ///
    /// ## General
    ///
    /// When specialising for these constructors, we
    /// want to be specialising for the actual underlying constructors.
    /// Naively, we would simply return the list of constructors they correspond
    /// to. We instead are more clever: if there are constructors that we
    /// know will behave the same wrt the current matrix, we keep them
    /// grouped. For example, all lists of a sufficiently large length will
    /// either be all useful or all non-useful with a given matrix.
    ///
    /// See the branches for details on how the splitting is done.
    ///
    /// ## Discarding constructors
    ///
    /// This function may discard some irrelevant constructors if this preserves
    /// behaviour and diagnostics. For example, for the `_` case, we ignore the
    /// constructors already present in the matrix, unless all of them are.
    pub(super) fn split<'a>(
        &self,
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) -> SmallVec<[Self; 1]> {
        match self {
            Constructor::Wildcard => {
                let mut split_wildcard = SplitWildcard::new(ctx);
                split_wildcard.split(ctx, ctors);
                split_wildcard.into_ctors(ctx)
            }
            // Fast track to just the single constructor if this range is trivial
            Constructor::IntRange(range) if !range.is_singleton() => {
                let mut split_range = SplitIntRange::new(range.clone());
                let int_ranges = ctors.filter_map(|ctor| ctor.as_int_range());

                split_range.split(int_ranges.cloned());
                split_range.iter().map(Constructor::IntRange).collect()
            }
            &Constructor::List(List { kind: ListKind::Var(prefix_len, suffix_len) }) => {
                let mut split_self = SplitVarList::new(prefix_len, suffix_len);

                let slices = ctors.filter_map(|c| c.as_list()).map(|s| s.kind);
                split_self.split(slices);
                split_self.iter().map(Constructor::List).collect()
            }
            // In any other case, the split just puts this constructor
            // into the
            _ => smallvec![self.clone()],
        }
    }

    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a
    /// subset of `other`. For the simple cases, this is simply checking for
    /// equality. For the "grouped" constructors, this checks for inclusion.
    #[inline]
    pub(super) fn is_covered_by(&self, ctx: PatCtx<'gs, 'ls, 'cd, 's>, other: &Self) -> bool {
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
            (Constructor::NonExhaustive, _) => false,

            _ => panic_on_span!(
                ctx.location(),
                ctx.source_map(),
                "trying to compare incompatible constructors {:?} and {:?}",
                self,
                other
            ),
        }
    }

    /// Faster version of `is_covered_by` when applied to many constructors.
    /// `used_ctors` is assumed to be built from `matrix.head_ctors()` with
    /// wildcards filtered out, and `self` is assumed to have been split
    /// from a wildcard.
    fn is_covered_by_any(
        &self,
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        used_ctors: &[Constructor],
    ) -> bool {
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
            // This constructor is never covered by anything else
            Constructor::NonExhaustive => false,
            Constructor::Str(_)
            | Constructor::Missing
            | Constructor::Wildcard
            | Constructor::Or => {
                panic_on_span!(ctx.location(), ctx.source_map(), "Unexpected ctor in all_ctors")
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Fields<'p> {
    fields: &'p [DeconstructedPat<'p>],
}

impl<'p, 'gs, 'ls, 'cd, 's> Fields<'p> {
    fn empty() -> Self {
        Fields { fields: &[] }
    }

    /// Returns the list of patterns.
    pub(super) fn iter_patterns<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> {
        self.fields.iter()
    }

    pub(super) fn from_iter(
        ctx: PatCtx<'gs, 'ls, 'cd, 's>,
        fields: impl IntoIterator<Item = DeconstructedPat<'p>>,
    ) -> Self {
        // let fields: &[_] = cx.pattern_arena.alloc_from_iter(fields);
        // Fields { fields }
        todo!()
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result must have a length of `ctor.arity()`.
    pub(super) fn wildcards(ctx: PatCtx<'gs, 'ls, 'cd, 's>, ctor: &Constructor) -> Self {
        match ctor {
            Constructor::Single => todo!(),
            Constructor::Variant(_) => todo!(),
            Constructor::List(_) => todo!(),
            Constructor::Str(..)
            | Constructor::IntRange(..)
            | Constructor::NonExhaustive
            | Constructor::Missing { .. }
            | Constructor::Wildcard => Fields::empty(),
            Constructor::Or => {
                panic!("called `Fields::wildcards` on an `Or` ctor")
            }
        }
    }
}

/// A [DeconstructedPat] is a representation of a [Constructor] that is split
/// between the constructor subject `ctor` and the `fields` that the constructor
/// holds.
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
    /// The type of the current deconstructed pattern
    ty: TermId,
    /// The [Span] of the current pattern.
    span: Span,
    /// Whether the current pattern is reachable.
    reachable: Cell<bool>,
}

impl<'p, 'gs, 'ls, 'cd, 's> DeconstructedPat<'p> {
    pub(super) fn new(ctor: Constructor, fields: Fields<'p>, ty: TermId, span: Span) -> Self {
        DeconstructedPat { ctor, fields, span, ty, reachable: Cell::new(false) }
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard(ty: TermId) -> Self {
        Self::new(Constructor::Wildcard, Fields::empty(), ty, DUMMY_SPAN)
    }

    pub(super) fn wild_from_ctor(ctx: PatCtx<'gs, 'ls, 'cd, 's>, ctor: Constructor) -> Self {
        let fields = Fields::wildcards(ctx, &ctor);

        DeconstructedPat::new(ctor, fields, ctx.ty, DUMMY_SPAN)
    }

    /// Clone this [DeconstructedPat] whilst also forgetting the reachability.
    pub(super) fn clone_and_forget_reachability(&self) -> Self {
        DeconstructedPat::new(self.ctor.clone(), self.fields, self.ty, self.span)
    }

    /// Expand an `or` pattern into a passed [Vec], whilst also
    /// applying the same operation on children patterns.
    fn expand(pat: &'p Pat, vec: &mut Vec<&'p Pat>) {
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
    fn flatten_or_pat(pat: &'p Pat) -> Vec<&'p Pat> {
        let mut pats = Vec::new();
        Self::expand(pat, &mut pats);
        pats
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn from_pat(ctx: PatCtx<'gs, 'ls, 'cd, 's>, pat: &'p Pat) -> Self {
        let make_pat = |pat| DeconstructedPat::from_pat(ctx, pat);

        // @@Todo: support int, and float ranges
        let (ctor, fields) = match pat.kind.as_ref() {
            PatKind::Spread | PatKind::Wild => (Constructor::Wildcard, Fields::empty()),
            PatKind::Constant { value } => {
                // This deals with `char` and `integer` types...
                let range = IntRange::from_constant(ctx, *value);
                (Constructor::IntRange(range), Fields::empty())
            }
            PatKind::Str { value } => (Constructor::Str(*value), Fields::empty()),
            PatKind::Variant { pats, .. } | PatKind::Leaf { pats } => {
                let reader = ctx.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level0(Level0Term::Tuple(TupleLit { members })) => {
                        let members = reader.get_args(*members);

                        // Create wild-cards for all of the tuple inner members
                        let mut wilds: SmallVec<[_; 2]> = members
                            .positional()
                            .iter()
                            .map(|member| DeconstructedPat::wildcard(member.value))
                            .collect();

                        for field in pats {
                            wilds[field.index] = make_pat(&field.pat);
                        }

                        let fields = Fields::from_iter(ctx, wilds);
                        (Constructor::Single, fields)
                    }
                    Term::Level0(Level0Term::Constructed(ConstructedTerm { subject, members })) => {
                        let ctor = match pat.kind.as_ref() {
                            PatKind::Variant { index, .. } => Constructor::Variant(*index),
                            PatKind::Leaf { .. } => Constructor::Single,
                            _ => unreachable!(),
                        };

                        let args = reader.get_args(*members);
                        let tys = args.positional().iter().map(|arg| arg.value);

                        let mut wilds: SmallVec<[_; 2]> =
                            tys.map(DeconstructedPat::wildcard).collect();

                        for field in pats {
                            wilds[field.index] = make_pat(&field.pat);
                        }

                        let fields = Fields::from_iter(ctx, wilds);
                        (ctor, fields)
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        ctx,
                        "Unexpected ty `{}` when deconstructing pattern {:?}",
                        ctx.for_fmt(ctx.ty),
                        pat
                    ),
                }
            }
            PatKind::List { prefix, spread, suffix } => {
                // If the list has a spread pattern, then it becomes variable length, otherwise
                // it remains as fixed-length.
                let kind = if spread.is_some() {
                    ListKind::Var(prefix.len(), suffix.len())
                } else {
                    ListKind::Fixed(prefix.len() + suffix.len())
                };

                let ctor = Constructor::List(List::new(kind));
                let fields = Fields::from_iter(ctx, prefix.iter().chain(suffix).map(make_pat));

                (ctor, fields)
            }
            PatKind::Or { .. } => {
                // here, we need to expand the or pattern, so that all of the
                // children patterns of the `or` become fields of the deconstructed
                // pat.
                let pats = Self::flatten_or_pat(pat);

                (Constructor::Or, Fields::from_iter(ctx, pats.into_iter().map(make_pat)))
            }
        };

        Self::new(ctor, fields, ctx.ty, pat.span)
    }

    pub(crate) fn to_pat(&self, ctx: PatCtx<'gs, 'ls, 'cd, 's>) -> Pat {
        let mut children = self.iter_fields().map(|p| p.to_pat(ctx));

        let kind = match &self.ctor {
            ctor @ (Constructor::Single | Constructor::Variant(_)) => {
                let reader = ctx.reader();

                match reader.get_term(self.ty) {
                    Term::Level0(Level0Term::Tuple(TupleLit { members })) => PatKind::Leaf {
                        pats: children
                            .enumerate()
                            .map(|(index, pat)| FieldPat { index, pat })
                            .collect(),
                    },
                    Term::Level0(Level0Term::Constructed(ConstructedTerm { subject, members })) => {
                        match reader.get_term(*subject) {
                            Term::Level1(Level1Term::NominalDef(id)) => {
                                let nominal_def = reader.get_nominal_def(*id);

                                let pats = children
                                    .enumerate()
                                    .map(|(index, pat)| FieldPat { index, pat })
                                    .collect_vec();

                                match nominal_def {
                                    NominalDef::Struct(_) => PatKind::Leaf { pats },
                                    NominalDef::Enum(_) => {
                                        let Constructor::Variant(index) = ctor else {
                                            unreachable!()
                                        };

                                        PatKind::Variant { def: *id, pats, index: *index }
                                    }
                                }
                            }
                            _ => tc_panic!(
                                subject,
                                ctx,
                                "Malformed constructed subject during pattern conversion"
                            ),
                        }
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        ctx,
                        "Unexpected ty `{}` when converting to pattern",
                        ctx.for_fmt(ctx.ty),
                    ),
                }
            }
            Constructor::IntRange(range) => range.to_pat(ctx),
            Constructor::Str(value) => PatKind::Str { value: *value },
            Constructor::List(List { kind }) => match kind {
                ListKind::Fixed(size) => {
                    PatKind::List { prefix: children.collect_vec(), spread: None, suffix: vec![] }
                }
                ListKind::Var(prefix, suffix) => {
                    let mut children = children.peekable();

                    // build the prefix and suffix components
                    let prefix: Vec<_> = children.by_ref().take(*prefix).collect();
                    let suffix: Vec<_> = children.collect();

                    // Create the `spread` dummy pattern
                    let spread =
                        Pat { span: DUMMY_SPAN, kind: Box::new(PatKind::Spread), has_guard: false };

                    PatKind::List { prefix, spread: Some(spread), suffix }
                }
            },
            Constructor::Wildcard | Constructor::NonExhaustive => PatKind::Wild,
            Constructor::Or => panic!("cannot convert an `or` deconstructed pat back into pat"),
            Constructor::Missing => panic!(
                "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug,
                `Missing` should have been processed in `apply_constructors`"
            ),
        };

        Pat { span: self.span, kind: Box::new(kind), has_guard: false }
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
                Fields::wildcards(ctx, other_ctor).iter_patterns().collect()
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
