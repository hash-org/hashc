//! Defines the [ConstRange] type which is used for constructing comparison
//! ranges and jump tables when lowering `match` blocks.

use std::cmp::Ordering;

use hash_ast::ast;
use hash_ir::ir::{compare_constant_values, Const};
use hash_tir::pats::RangePat;

use crate::build::BodyBuilder;

/// A constant range which is a representation of a range pattern, but
/// instead of using literals, we directly store these with [Const]s.
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
    pub end: ast::RangeEnd,
}

impl ConstRange {
    /// Create a [ConstRange] from [RangePat].
    pub fn from_range(range: &RangePat, builder: &BodyBuilder) -> Self {
        let (lo, _) = builder.evaluate_const_pat(range.start);
        let (hi, _) = builder.evaluate_const_pat(range.end);

        Self { lo, hi, end: range.range_end }
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
                    (Less, _) | (Equal, ast::RangeEnd::Included)
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
                    (Less, _) | (Equal, ast::RangeEnd::Included)
                ),
        )
    }
}
