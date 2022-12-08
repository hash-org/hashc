//! Various utilities used for lowering `match` blocks.

use std::cmp::Ordering;

use hash_ast::ast::RangeEnd;
use hash_ir::ir::{compare_constant_values, Const};
use hash_types::{pats::RangePat, storage::GlobalStorage};

use crate::build::ty::evaluate_int_lit_term;

/// A constant range which is a representation of a range pattern, but
/// instead of using [TermId]s, we directly store these with [Const]s.
///
/// N.B. These [Const]s must be of the same type, and must be integral
///      types.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct ConstRange {
    /// The lower value of the range.
    pub lo: Const,
    /// The upper value of the range.
    pub hi: Const,
    /// If the range includes the `hi` or not.
    pub end: RangeEnd,
}

impl ConstRange {
    /// Create a [ConstRange] from [PatRange].
    pub fn from_range(range: &RangePat, tcx: &GlobalStorage) -> Self {
        let (lo, _) = evaluate_int_lit_term(range.lo, tcx);
        let (hi, _) = evaluate_int_lit_term(range.hi, tcx);

        Self { lo, hi, end: range.end }
    }

    /// Check if a [Const] is within the range.
    pub fn contains(&self, value: Const) -> Option<bool> {
        use Ordering::*;

        // If the range end is included, the value must be less than
        // or equal to the value.
        Some(
            matches!(compare_constant_values(self.lo, value)?, Less | Equal)
                && matches!(
                    (compare_constant_values(self.hi, value)?, self.end),
                    (Less, _) | (Equal, RangeEnd::Included)
                ),
        )
    }

    /// Check if a range overlaps with another range.
    pub fn overlaps(&self, other: &Self) -> Option<bool> {
        use Ordering::*;

        // self.lo <= other.hi && self.hi >= other.lo
        Some(
            matches!(compare_constant_values(self.lo, other.hi)?, Less | Equal)
                && matches!(
                    (compare_constant_values(self.hi, other.lo)?, self.end),
                    (Less, _) | (Equal, RangeEnd::Included)
                ),
        )
    }
}
