//! Exhaustiveness representation of ranges, which also include
//! integer, and character literals.
//!
//! # Constructor splitting
//!
//! The idea is as follows: given a constructor `c` and a matrix, we want to
//! specialise in turn with all the value constructors that are covered by `c`,
//! and compute usefulness for each. Instead of listing all those constructors
//! (which is intractable), we group those value constructors together as much
//! as possible. Example:
//!
//! ```ignore
//! match (0, false) {
//!     (0 ..=100, true) => {} // `p_1`
//!     (50..=150, false) => {} // `p_2`
//!     (0 ..=200, _) => {} // `q`
//! }
//! ```
//!
//! The naive approach would try all numbers in the range `0..=200`. But we can
//! be a lot more clever: `0` and `1` for example will match the exact same
//! rows, and return equivalent witnesses. In fact all of `0..50` would. We can
//! thus restrict our exploration to 4 constructors: `0..50`, `50..=100`,
//! `101..=150` and `151..=200`. That is enough and infinitely more tractable.
//!
//! We capture this idea in a function `split(p_1 ... p_n, c)` which returns a
//! list of constructors `c'` covered by `c`. Given such a `c'`, we require that
//! all value ctors `c''` covered by `c'` return an equivalent set of witnesses
//! after specializing and computing usefulness. In the example above, witnesses
//! for specializing by `c''` covered by `0..50` will only differ in their first
//! element.
use std::{
    cmp::{max, min},
    fmt,
    iter::once,
};

use hash_ast::ast::RangeEnd;

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::{constant::Constant, PatCtx},
    ops::AccessToOps,
    storage::{
        primitives::{Level0Term, LitTerm, Term},
        AccessToStorage, StorageRef,
    },
};

/// The [IntRange] is used as a structure to represent `integral` types like
/// signed integers, unsigned integers, characters and of-course range patterns
/// which are represented in this format. [IntRange] is a useful abstraction to
/// represent these data types rather than listing all of the possible
/// constructors that these data types have.
#[derive(Clone, Copy)]

pub struct IntRange {
    pub(super) start: u128,
    pub(super) end: u128,

    /// Keeps the bias used for encoding the range. It depends on the type of
    /// the range and possibly the pointer size of the current architecture.
    /// The algorithm ensures we never compare `IntRange`s with different
    /// types/architectures.
    pub bias: u128,
}

impl IntRange {
    /// Get the boundaries of the current [IntRange]
    pub fn boundaries(&self) -> (u128, u128) {
        (self.start, self.end)
    }

    /// Check whether `self` is covered by the other range, in other words
    /// if other is a super-range of `self`.
    pub fn is_subrange(&self, other: &Self) -> bool {
        other.start <= self.start && self.end <= other.end
    }

    /// Get the intersection between `self` and `other` [IntRange]s.
    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let (lo, hi) = self.boundaries();
        let (other_lo, other_hi) = other.boundaries();

        if lo <= other_hi && other_lo <= hi {
            Some(IntRange { start: max(lo, other_lo), end: min(hi, other_hi), bias: self.bias })
        } else {
            None
        }
    }

    /// Check whether the [IntRange] is a singleton, or in other words if there
    /// is only one step within the range
    pub fn is_singleton(&self) -> bool {
        self.start == self.end
    }

    /// If the `other` range covers all possible values of this [IntRange], then
    /// we conclude that the the `other` range covers the range. This function
    /// is used by [`super::construct::ConstructorOps::is_covered_by`].
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
        let (lo, hi) = Self::to_borders(self.range);
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
                let (start, end) = match (prev_border, border) {
                    (IntBorder::JustBefore(n), IntBorder::JustBefore(m)) if n < m => (n, (m - 1)),
                    (IntBorder::JustBefore(n), IntBorder::AfterMax) => (n, u128::MAX),
                    _ => unreachable!(), // Ruled out by the sorting and filtering we did
                };
                IntRange { start, end, bias: self.range.bias }
            })
    }
}

pub struct IntRangeOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for IntRangeOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> IntRangeOps<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Attempt to build a [IntRange] from a provided constant.
    #[inline]
    pub fn range_from_constant(&self, constant: Constant) -> IntRange {
        let reader = self.reader();

        let bias: u128 = match reader.get_term(constant.ty) {
            Term::Level0(Level0Term::Lit(lit)) => match lit {
                LitTerm::Int { kind, .. } if kind.is_signed() => {
                    // @@Future: support `ibig` here
                    let size = kind.size().unwrap();
                    1u128 << (size * 8 - 1)
                }
                LitTerm::Char(_) | LitTerm::Int { .. } => 0,
                LitTerm::Str(_) => panic!("got `str` in const!"),
            },
            _ => tc_panic!(
                constant.ty,
                self,
                "got unexpected ty `{}` when reading Constant.",
                self.for_fmt(constant.ty)
            ),
        };

        // read from the constant the actual bits and apply bias
        let val = constant.data() ^ bias;
        IntRange { start: val, end: val, bias }
    }

    /// Create an [IntRange] from two specified bounds, and assuming that the
    /// type is an integer (of the column)
    pub(crate) fn make_range(&self, ctx: PatCtx, lo: u128, hi: u128, end: &RangeEnd) -> IntRange {
        let bias = self.signed_bias(ctx);

        let (lo, hi) = (lo ^ bias, hi ^ bias);
        let offset = (*end == RangeEnd::Excluded) as u128;
        if lo > hi || (lo == hi && *end == RangeEnd::Excluded) {
            panic!("malformed range pattern: {}..{}", lo, (hi - offset));
        }

        IntRange { start: lo, end: hi - offset, bias }
    }

    /// Get the bias based on the type, if it is a signed, integer then
    /// the bias is set to be just at the end of the signed boundary
    /// of the integer size, in other words at the position where the
    /// last byte is that identifies the sign.
    fn signed_bias(&self, ctx: PatCtx) -> u128 {
        // @@Future: support `ibig` here
        if let Some(ty) = self.oracle().term_as_int_ty(ctx.ty) {
            if let Some(size) = ty.size() && ty.is_signed()  {
                let bits = (size * 8) as u128;
                return 1u128 << (bits - 1);
            }
        };

        0
    }
}
