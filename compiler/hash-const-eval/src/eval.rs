//! Module which contains implementation and utilities for constant
//! propagation and constant folding optimisations that can occur on
//! Hash IR.

use hash_layout::{
    compute::LayoutComputer,
    constant::{Const, ConstKind},
    ty::{ReprTy, ReprTyId},
};
use hash_source::{constant::Scalar, FloatTy, Size};
use hash_storage::store::statics::StoreId;
use hash_target::data_layout::HasDataLayout;
use hash_utils::{derive_more::Constructor, num_traits};

use crate::op::{BinOp, UnOp};

/// A constant folder which is used to fold constants into a single
/// constant.
#[derive(Constructor)]
pub struct ConstFolder<'ctx> {
    lc: LayoutComputer<'ctx>,
}

type OverflowingOp = fn(i128, i128) -> (i128, bool);

impl<'ctx> ConstFolder<'ctx> {
    /// Attempt to evaluate two [Const]s and a binary operator.
    pub fn try_fold_bin_op(&self, op: BinOp, lhs: &Const, rhs: &Const) -> Option<Const> {
        // If the two constants are non-scalar, then we abort the folding...
        let (ConstKind::Scalar(left), ConstKind::Scalar(right)) = (lhs.kind(), rhs.kind()) else {
            return None;
        };

        let (l_ty, r_ty) = (lhs.ty(), rhs.ty());

        match l_ty.value() {
            ty if ty.is_integral() => {
                let size = self.lc.size_of_ty(l_ty).ok()?;
                let l_bits = left.to_bits(size).ok()?;
                let r_bits = right.to_bits(size).ok()?;
                self.binary_int_op(op, l_ty, l_bits, r_ty, r_bits)
            }
            ReprTy::Float(fl_ty) => match fl_ty {
                FloatTy::F32 => Self::binary_float_op(op, left.to_f32(), left.to_f32()),
                FloatTy::F64 => Self::binary_float_op(op, left.to_f64(), left.to_f64()),
            },
            ReprTy::Bool => {
                let l: bool = left.try_into().ok()?;
                let r: bool = right.try_into().ok()?;
                Self::binary_bool_op(op, l, r)
            }
            ReprTy::Char => {
                let l: char = left.try_into().ok()?;
                let r: char = right.try_into().ok()?;
                Self::binary_char_op(op, l, r)
            }
            _ => None,
        }
    }

    fn binary_bool_op(bin_op: BinOp, lhs: bool, rhs: bool) -> Option<Const> {
        use crate::op::BinOp::*;

        Some(match bin_op {
            Gt => Const::bool(lhs & !rhs),
            GtEq => Const::bool(lhs >= rhs),
            Lt => Const::bool(!lhs & rhs),
            LtEq => Const::bool(lhs <= rhs),
            Eq => Const::bool(lhs == rhs),
            Neq => Const::bool(lhs != rhs),
            BitAnd => Const::bool(lhs & rhs),
            BitOr => Const::bool(lhs | rhs),
            BitXor => Const::bool(lhs ^ rhs),
            _ => panic!("invalid operator `{bin_op}` for boolean operands"),
        })
    }

    /// Perform an operation on two character constants.
    ///
    /// ##Note: This only supports comparison operators, thus the output is always
    /// a boolean constant.
    fn binary_char_op(bin_op: BinOp, lhs: char, rhs: char) -> Option<Const> {
        use crate::op::BinOp::*;

        Some(match bin_op {
            Gt => Const::bool(lhs > rhs),
            GtEq => Const::bool(lhs >= rhs),
            Lt => Const::bool(lhs < rhs),
            LtEq => Const::bool(lhs <= rhs),
            Eq => Const::bool(lhs == rhs),
            Neq => Const::bool(lhs != rhs),
            _ => panic!("invalid operator `{bin_op}` for boolean operands"),
        })
    }

    /// Perform an operation on two integer constants. This accepts the raw bits
    /// of the integer, and the size of the integer.
    fn binary_int_op(
        &self,
        bin_op: BinOp,
        lhs_ty: ReprTyId,
        lhs: u128,
        rhs_ty: ReprTyId,
        rhs: u128,
    ) -> Option<Const> {
        use crate::op::BinOp::*;

        debug_assert_eq!(lhs_ty, rhs_ty);
        let size = self.lc.size_of_ty(lhs_ty).ok()?;

        // We have to handle `shl` and `shr` differently since they have different
        // operand types.
        //
        // This matches the codegen implementation:
        // - compiler/hash-codegen/src/lower/rvalue.rs#63-85
        //
        if matches!(bin_op, Shl | Shr) {
            let size_bits = u128::from(size.bits());

            // We have to ensure that the operand size is smaller
            // than 128 bits, otherwise we will panic. This is because
            // types that are larger than 128 bits (i.e. 256bit integers)
            // would behave differently than expected. For example, if we
            // had a shift by -1i8 would actually shift by (255), but would *not*
            // be considered an overflow. A shiift by `-1i16` would however be
            // considered as an ovrflow. For integers that are `i512`, then a shift by
            // `-i18` would produce a different result than one by `-1i16`:
            //
            // - The first shhifts by 255, and the later by u16::MAX % 512 = 511.
            //
            // For this reason, integers that are bigger than i128 with negative operand
            // shifts will always overflow.
            //
            // @@Future: when we implement larger bit widths, we have to properly consider
            // that some operands (that are negative) now have the possibility
            // of not overflowing and consequently we will have to change the
            // implementation here.
            assert!(size_bits <= 128);

            let overflow = rhs >= size_bits;
            let rhs = rhs % size_bits;
            let rhs = u32::try_from(rhs).unwrap(); // This is masked so it will always fit.

            let result = if lhs_ty.is_signed() {
                let lhs = size.sign_extend(lhs) as i128;
                let result = match bin_op {
                    Shl => lhs.checked_shl(rhs).unwrap(),
                    Shr => lhs.checked_shr(rhs).unwrap(),
                    _ => panic!("unexpected operator"),
                };

                result as u128
            } else {
                match bin_op {
                    Shl => lhs.checked_shl(rhs).unwrap(),
                    Shr => lhs.checked_shr(rhs).unwrap(),
                    _ => panic!("unexpected operator"),
                }
            };

            let truncated = size.truncate(result);

            if overflow {
                // @@ErrorHandling @@UB: we should somehow emit an error!
                return None;
            }

            return Some(Const::new(lhs_ty, ConstKind::Scalar(Scalar::from_uint(truncated, size))));
        }

        // If the type is signed, we have to handle comparisons and arithmetic
        // operations differently.
        if lhs_ty.is_signed() {
            // Handle binary comparison operators first...
            let op: Option<fn(&i128, &i128) -> bool> = match bin_op {
                Gt => Some(i128::gt),
                GtEq => Some(i128::ge),
                Lt => Some(i128::lt),
                LtEq => Some(i128::le),
                Eq => Some(i128::eq),
                Neq => Some(i128::ne),
                _ => None,
            };

            if let Some(op) = op {
                // Sign extend the two values to become i128s.
                let left = size.sign_extend(lhs) as i128;
                let right = size.sign_extend(rhs) as i128;
                return Some(Const::bool(op(&left, &right)));
            }

            // The we get the function to perform the operation on the
            // two signed integers.
            let op: Option<OverflowingOp> = match bin_op {
                Add => Some(i128::overflowing_add),
                Sub => Some(i128::overflowing_sub),
                Mul => Some(i128::overflowing_mul),
                // @@ErrorHandling @@UB: we should somehow emit an error saying that a
                // constant operation is divide by zero, and this is UB at runtime!!!
                Div if rhs == 0 => return None,
                Mod if rhs == 0 => return None,
                Div => Some(i128::overflowing_div),
                Mod => Some(i128::overflowing_rem),
                _ => None,
            };

            if let Some(op) = op {
                let left = size.sign_extend(lhs) as i128;
                let right = size.sign_extend(rhs) as i128;

                // @@ErrorHandling @@UB: we should somehow emit an error saying that a
                // constant operation overflowed, and this is UB at runtime!!!
                if matches!(bin_op, Div | Mod) && left == size.signed_int_min() && right == -1 {
                    return None;
                }

                // Compute the result, truncate and convert into a Scalar.
                let (result, overflow) = op(left, right);
                let result = result as u128;
                let truncated = size.truncate(result);
                let overflow = overflow || size.sign_extend(truncated) != result;

                // @@ErrorHandling @@UB: we should somehow emit an error saying that a
                // constant operation overflowed, and this is UB at runtime!!!
                if overflow {
                    return None;
                }

                return Some(Const::new(
                    lhs_ty,
                    ConstKind::Scalar(Scalar::from_uint(truncated, size)),
                ));
            }
        }

        let dl = self.lc.data_layout();

        match bin_op {
            Eq => Some(Const::bool(lhs == rhs)),
            Neq => Some(Const::bool(lhs != rhs)),
            Gt => Some(Const::bool(lhs > rhs)),
            GtEq => Some(Const::bool(lhs >= rhs)),
            Lt => Some(Const::bool(lhs < rhs)),
            LtEq => Some(Const::bool(lhs <= rhs)),
            BitOr => Some(Const::from_scalar_like(lhs | rhs, lhs_ty, dl)),
            BitAnd => Some(Const::from_scalar_like(lhs & rhs, lhs_ty, dl)),
            BitXor => Some(Const::from_scalar_like(lhs ^ rhs, lhs_ty, dl)),
            Add | Sub | Mul | Div | Mod => {
                let op: fn(u128, u128) -> (u128, bool) = match bin_op {
                    Add => u128::overflowing_add,
                    Sub => u128::overflowing_sub,
                    Mul => u128::overflowing_mul,
                    // @@ErrorHandling @@UB: we should somehow emit an error saying that a
                    // constant operation is divide by zero, and this is UB at runtime!!!
                    Div if rhs == 0 => return None,
                    Mod if rhs == 0 => return None,
                    Div => u128::overflowing_div,
                    Mod => u128::overflowing_rem,
                    _ => unreachable!(),
                };

                // Compute the result, truncate and convert into a Scalar.
                let (result, overflow) = op(lhs, rhs);
                let truncated = size.truncate(result);
                let overflow = overflow || truncated != result;

                // @@ErrorHandling @@UB: we should somehow emit an error saying that a
                // constant operation overflowed, and this is UB at runtime!!!
                if overflow {
                    return None;
                }

                Some(Const::new(lhs_ty, ConstKind::Scalar(Scalar::from_uint(truncated, size))))
            }
            Exp => None,
            _ => panic!("invalid operator, `{bin_op}` should have been handled"),
        }
    }

    /// Perform an operation on two floating point constants.
    fn binary_float_op<F: num_traits::Float + Into<Const>>(
        op: BinOp,
        lhs: F,
        rhs: F,
    ) -> Option<Const> {
        Some(match op {
            BinOp::Gt => Const::bool(lhs > rhs),
            BinOp::GtEq => Const::bool(lhs >= rhs),
            BinOp::Lt => Const::bool(lhs < rhs),
            BinOp::LtEq => Const::bool(lhs <= rhs),
            BinOp::Eq => Const::bool(lhs == rhs),
            BinOp::Neq => Const::bool(lhs != rhs),
            BinOp::Add => (lhs + rhs).into(),
            BinOp::Sub => (lhs - rhs).into(),
            BinOp::Mul => (lhs * rhs).into(),
            BinOp::Div => (lhs / rhs).into(),
            BinOp::Mod => (lhs % rhs).into(),
            BinOp::Exp => (lhs.powf(rhs)).into(),

            // No other operations can be performed on floats
            _ => return None,
        })
    }

    pub fn try_fold_un_op(&self, op: UnOp, operand: &Const) -> Option<Const> {
        // If the two constants are non-scalar, then we abort the folding... @@Future:
        // do we need this?
        let ConstKind::Scalar(scalar) = operand.kind() else {
            return None;
        };

        let ty = operand.ty();

        match ty.value() {
            t if t.is_integral() => {
                let size = self.lc.size_of_ty(ty).ok()?;
                let bits = scalar.to_bits(size).ok()?;
                self.unary_int_op(op, ty, size, bits)
            }
            ReprTy::Float(fl_ty) => match fl_ty {
                FloatTy::F32 => Self::unary_float_op(op, scalar.to_f32()),
                FloatTy::F64 => Self::unary_float_op(op, scalar.to_f64()),
            },
            ReprTy::Bool => {
                let l: bool = scalar.try_into().ok()?;
                Self::unary_bool_op(op, l)
            }
            _ => None,
        }
    }

    fn unary_int_op(&self, op: UnOp, ty: ReprTyId, size: Size, operand: u128) -> Option<Const> {
        use crate::op::UnOp::*;

        // @@Overflow: properly deal and communicate that an
        // overflow has occurred.
        let (val, _overflow) = match op {
            Neg => {
                assert!(ty.borrow().is_signed());
                let value = size.sign_extend(operand) as i128;
                let (res, overflow) = value.overflowing_neg();
                let res = res as u128;
                let truncated = size.truncate(res);

                (truncated, overflow || size.sign_extend(res) != res)
            }
            BitNot | Not => (size.truncate(!operand), false),
        };

        Some(Const::new(ty, ConstKind::Scalar(Scalar::from_uint(val, size))))
    }

    fn unary_float_op<F: num_traits::Float + Into<Const>>(op: UnOp, operand: F) -> Option<Const> {
        match op {
            UnOp::Neg => Some((-operand).into()),
            _ => None,
        }
    }

    fn unary_bool_op(op: UnOp, operand: bool) -> Option<Const> {
        match op {
            UnOp::Not => Some(Const::bool(!operand)),
            _ => None,
        }
    }
}
