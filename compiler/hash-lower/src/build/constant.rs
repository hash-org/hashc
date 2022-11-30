//! Utilities and operations that involve [Const]s when lowering expressions.
//! This module also includes logic that can perform constant folding on
//! various constants.

use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

use hash_ast::ast::{AstNodeRef, Lit};
use hash_ir::ir::{self, BinOp, Const};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    constant::{FloatConstant, FloatConstantValue, IntConstant, CONSTANT_MAP},
    identifier::IDENTS,
};

use super::Builder;

impl<'tcx> Builder<'tcx> {
    /// Lower a simple literal into an [ir::Const], this does not deal
    /// with literals that are arrays or other compound data structures.
    pub(crate) fn as_constant(&mut self, lit: AstNodeRef<'tcx, Lit>) -> ir::Const {
        match lit.body {
            Lit::Str(literal) => ir::Const::Str(literal.data),
            Lit::Char(literal) => ir::Const::Char(literal.data),
            Lit::Int(literal) => ir::Const::Int(literal.value),
            Lit::Float(literal) => ir::Const::Float(literal.value),
            Lit::Bool(literal) => ir::Const::Byte(literal.data.into()),
            Lit::Set(_) | Lit::Map(_) | Lit::List(_) | Lit::Tuple(_) => {
                panic_on_span!(
                    lit.span().into_location(self.source_id),
                    self.source_map,
                    "cannot lower non-primitive literal into constant"
                )
            }
        }
    }

    /// Function that attempts to fold a constant operation. The function
    /// expects that the provided [Const]s are of integral kind i.e.
    /// `float`, `int`, or `char` and then tries to perform the operation on
    /// them. If the operation is not possible, then the function will
    /// return [None].
    pub(crate) fn try_fold_const_op(&mut self, op: BinOp, lhs: Const, rhs: Const) -> Option<Const> {
        // @@Todo: for now we only handle `small` values of integer types, in the
        // future we should also be able to perform folds on `ibig` and `ubig` values.
        if let Const::Int(interned_lhs) = lhs && let Const::Int(interned_rhs) = rhs &&
            CONSTANT_MAP.map_int_constant(interned_lhs, |v| v.is_small()) &&
            CONSTANT_MAP.map_int_constant(interned_rhs, |v| v.is_small())
        {
            let lhs_const = CONSTANT_MAP.lookup_int_constant(interned_lhs);
            let rhs_const = CONSTANT_MAP.lookup_int_constant(interned_rhs);

            // First we need to coerce the types into the same primitive integer type, we do this 
            // by checking the `suffix` and then coercing both ints into that value
            return match lhs_const.suffix.unwrap_or(IDENTS.i32) {
                i if i == IDENTS.i8 => fold_int_const(op, TryInto::<i8>::try_into(lhs_const).unwrap(), TryInto::<i8>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.i16 => fold_int_const(op, TryInto::<i16>::try_into(lhs_const).unwrap(), TryInto::<i16>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.i32 => fold_int_const(op, TryInto::<i32>::try_into(lhs_const).unwrap(), TryInto::<i32>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.i64 => fold_int_const(op, TryInto::<i64>::try_into(lhs_const).unwrap(), TryInto::<i64>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.isize => fold_int_const(op, TryInto::<isize>::try_into(lhs_const).unwrap(), TryInto::<isize>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.u8 => fold_int_const(op, TryInto::<u8>::try_into(lhs_const).unwrap(), TryInto::<u8>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.u16 => fold_int_const(op, TryInto::<u16>::try_into(lhs_const).unwrap(), TryInto::<u16>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.u32 => fold_int_const(op, TryInto::<u32>::try_into(lhs_const).unwrap(), TryInto::<u32>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.u64 => fold_int_const(op, TryInto::<u64>::try_into(lhs_const).unwrap(), TryInto::<u64>::try_into(rhs_const).unwrap()),
                i if i == IDENTS.usize => fold_int_const(op, TryInto::<usize>::try_into(lhs_const).unwrap(), TryInto::<usize>::try_into(rhs_const).unwrap()),
                _ => unreachable!(),
            }
        }

        // Check if these two operands are floating point numbers
        if let Const::Float(interned_lhs) = lhs && let Const::Float(interned_rhs) = rhs {
            let lhs_const = CONSTANT_MAP.lookup_float_constant(interned_lhs);
            let rhs_const = CONSTANT_MAP.lookup_float_constant(interned_rhs);

            return match (lhs_const.value, rhs_const.value) {
                (FloatConstantValue::F32(lhs), FloatConstantValue::F32(rhs)) => fold_float_const(op, lhs, rhs),
                (FloatConstantValue::F64(lhs), FloatConstantValue::F64(rhs)) => fold_float_const(op, lhs, rhs),
                _ => unreachable!(),
            }
        }

        None
    }
}

/// Function that will take two operands and perform a binary operation on them
/// whilst yielding a [Const] value. If the operation is not possible, then the
/// function will return [None].
fn fold_int_const<T>(op: BinOp, lhs: T, rhs: T) -> Option<Const>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitAnd<Output = T>
        + BitOr<Output = T>
        + BitXor<Output = T>
        + Shl<Output = T>
        + Shr<Output = T>
        + PartialEq
        + PartialOrd
        + Into<IntConstant>,
{
    let value: Option<T> = match op {
        BinOp::Gt => return Some(Const::Byte((lhs > rhs).into())),
        BinOp::GtEq => return Some(Const::Byte((lhs >= rhs).into())),
        BinOp::Lt => return Some(Const::Byte((lhs < rhs).into())),
        BinOp::LtEq => return Some(Const::Byte((lhs <= rhs).into())),
        BinOp::EqEq => return Some(Const::Byte((lhs == rhs).into())),
        BinOp::NotEq => return Some(Const::Byte((lhs != rhs).into())),
        BinOp::Add => Some(lhs + rhs),
        BinOp::Sub => Some(lhs - rhs),
        BinOp::Mul => Some(lhs * rhs),
        BinOp::Div => Some(lhs / rhs),
        BinOp::Mod => Some(lhs % rhs),

        BinOp::BitAnd => Some(lhs & rhs),
        BinOp::BitOr => Some(lhs | rhs),
        BinOp::BitXor => Some(lhs ^ rhs),
        BinOp::Shl => Some(lhs << rhs),
        BinOp::Shr => Some(lhs >> rhs),

        // Don't do anything for exponents, since not all integral kinds support this.
        BinOp::Exp => None,

        // We don't deal with logical operations here since these are
        // not integral operations
        BinOp::Or | BinOp::And => None,
    };

    value.map(|val| {
        // Create the new constant value and return it as a `const`
        let value: IntConstant = val.into();
        let id = CONSTANT_MAP.create_int_constant(value);
        Const::Int(id)
    })
}

/// Function that will take two operands of a [FloatConstant] kind and perform a
/// binary operation on them whilst yielding a [Const] value. If the operation
/// is not possible, then the function will return [None].
fn fold_float_const<T>(op: BinOp, lhs: T, rhs: T) -> Option<Const>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + num_traits::float::Float
        + PartialEq
        + PartialOrd
        + Into<FloatConstant>,
{
    let value = match op {
        BinOp::Gt => return Some(Const::Byte((lhs > rhs).into())),
        BinOp::GtEq => return Some(Const::Byte((lhs >= rhs).into())),
        BinOp::Lt => return Some(Const::Byte((lhs < rhs).into())),
        BinOp::LtEq => return Some(Const::Byte((lhs <= rhs).into())),
        BinOp::EqEq => return Some(Const::Byte((lhs == rhs).into())),
        BinOp::NotEq => return Some(Const::Byte((lhs != rhs).into())),
        BinOp::Add => Some(lhs + rhs),
        BinOp::Sub => Some(lhs - rhs),
        BinOp::Mul => Some(lhs * rhs),
        BinOp::Div => Some(lhs / rhs),
        BinOp::Mod => Some(lhs % rhs),
        BinOp::Exp => Some(lhs.powf(rhs)),

        // No other operations can be performed on floats
        _ => None,
    };

    value.map(|val| {
        // Create the new constant value and return it as a `const`
        let value: FloatConstant = val.into();
        let id = CONSTANT_MAP.create_float_constant(value);
        Const::Float(id)
    })
}
