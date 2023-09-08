//! Defines the [ConstRange] type which is used for constructing comparison
//! ranges and jump tables when lowering `match` blocks.

use std::cmp::Ordering;

use hash_ast::ast;
use hash_ir::{ir::Const, ty::IrTyId};
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

    /// The type of the range. This is stored for convience when computing
    /// the range.
    pub ty: IrTyId,
}

impl ConstRange {
    /// Create a [ConstRange] from [RangePat].
    pub fn from_range(range: &RangePat, ty: IrTyId, builder: &BodyBuilder) -> Self {
        let (lo, _) = builder.evaluate_range_lit(range.lo, ty, false);
        let (hi, _) = builder.evaluate_range_lit(range.hi, ty, true);

        Self { lo, hi, end: range.end, ty }
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

/// This performs a shallow [Const] comparison that checks if two constants are the 
/// same. This is only used when checking various properties of [ConstRange] and shouldn't 
/// be used as a general purpose "comparison" function for constants.
/// 
/// ##Note: This will panic if the constants below are larger than 128bits in size. This 
/// is mostly intended for scalars.
pub fn compare_constant_values(left: Const, right: Const) -> Option<Ordering> {
    match (left, right) {
        (Const::Zero(_), Const::Zero(_)) => Some(Ordering::Equal),
        (Const::Bool(left), Const::Bool(right)) => Some(left.cmp(&right)),
        (Const::Char(left), Const::Char(right)) => Some(left.cmp(&right)),
        (Const::Int(left), Const::Int(right)) => {
            left.map(|left| right.map(|right| left.partial_cmp(right)))
        }
        (Const::Float(left), Const::Float(right)) => {
            left.map(|left| right.map(|right| left.partial_cmp(right)))
        }
        (Const::Str(left), Const::Str(right)) => Some(left.cmp(&right)),
        _ => None,
    }
}
