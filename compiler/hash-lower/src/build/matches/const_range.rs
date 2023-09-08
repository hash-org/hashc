//! Defines the [ConstRange] type which is used for constructing comparison
//! ranges and jump tables when lowering `match` blocks.

use std::cmp::Ordering;

use hash_ast::ast;
use hash_ir::{
    constant::{self, ConstKind},
    ir::Const,
    ty::{IrTy, IrTyId},
};
use hash_ir_utils::const_utils::ConstUtils;
use hash_layout::compute::LayoutComputer;
use hash_storage::store::statics::StoreId;
use hash_target::{data_layout::HasDataLayout, primitives::FloatTy};
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
        let (lo, _) = builder.eval_range_lit(range.lo, ty, false);
        let (hi, _) = builder.eval_range_lit(range.hi, ty, true);

        Self { lo, hi, end: range.end, ty }
    }

    /// Check if a [Const] is within the range.
    pub fn contains(&self, value: Const, _lc: LayoutComputer<'_>) -> Option<bool> {
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
    pub fn overlaps(&self, other: &Self, _lc: LayoutComputer<'_>) -> Option<bool> {
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

/// This performs a shallow [Const] comparison that checks if two constants are
/// the same. This is only used when checking various properties of [ConstRange]
/// and shouldn't be used as a general purpose "comparison" function for
/// constants.
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

/// This performs a shallow [Const] comparison that checks if two constants are
/// the same. This is only used when checking various properties of [ConstRange]
/// and shouldn't be used as a general purpose "comparison" function for
/// constants.
///
/// ##Note: This will panic if the constants below are larger than 128bits in size. This
/// is mostly intended for scalars.
pub fn _compare_const_values(
    left: &constant::Const,
    right: &constant::Const,
    lc: LayoutComputer<'_>,
) -> Option<Ordering> {
    // The type of the constants should be the same...
    debug_assert_eq!(left.ty(), right.ty(), "const types are not equal");

    let ty = left.ty().value();

    // In the case that the type is a trivial char, we can do a direct scalar
    // compare and avoid the extra work.
    match ty {
        IrTy::Int(_) | IrTy::Float(_) => {}
        _ => {
            if let (ConstKind::Scalar(left_s), ConstKind::Scalar(right_s)) =
                (left.kind(), right.kind())
            {
                return Some(left_s.cmp(&right_s));
            }
        }
    };

    // Evaluate the bits of the constant, this implies that they will be
    // converted to a scalar value. If they are non-scalar then something went
    // wrong!
    let left = ConstUtils::new(lc, left).eval_bits();
    let right = ConstUtils::new(lc, right).eval_bits();

    match ty {
        IrTy::Int(ty) => {
            let size = ty.size(lc.data_layout().pointer_size);
            let a = size.sign_extend(left);
            let b = size.sign_extend(right);
            Some((a as i128).cmp(&(b as i128)))
        }
        IrTy::Float(FloatTy::F32) => {
            let a = f32::from_bits(left as u32);
            let b = f32::from_bits(left as u32);
            a.partial_cmp(&b)
        }
        IrTy::Float(FloatTy::F64) => {
            let a = f64::from_bits(left as u64);
            let b = f64::from_bits(left as u64);
            a.partial_cmp(&b)
        }

        // Fallback onto just comparing the bits.
        _ => Some(left.cmp(&right)),
    }
}
