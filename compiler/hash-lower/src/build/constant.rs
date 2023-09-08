//! Utilities and operations that involve [Const]s when lowering expressions.
//! This module also includes logic that can perform constant folding on
//! various constants.

use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

use hash_ast::ast::AstNodeId;
use hash_ir::ir::{self, BinOp, Const};
use hash_reporting::macros::panic_on_span;
use hash_source::constant::{FloatConstant, FloatConstantValue, IntConstant, InternedFloat};
use hash_storage::store::statics::StoreId;
use hash_tir::{
    lits::{Lit, LitId},
    terms::Term,
};

use super::BodyBuilder;

/// Convert a [LitId] into an [ir::Const].
#[inline]
pub fn lit_to_const(lit: LitId) -> ir::Const {
    match *lit.value() {
        Lit::Int(lit) => ir::Const::Int(lit.interned_value()),
        Lit::Str(lit) => ir::Const::Str(lit.interned_value()),
        Lit::Char(lit) => ir::Const::Char(lit.value()),
        Lit::Float(lit) => ir::Const::Float(lit.interned_value()),
    }
}

impl<'tcx> BodyBuilder<'tcx> {
    /// Lower a simple literal into an [ir::Const], this does not deal
    /// with literals that are arrays or other compound data structures.
    pub(crate) fn as_constant(&mut self, lit: LitId) -> Const {
        lit_to_const(lit)
    }

    /// Lower a constant expression, i.e. a literal value.
    pub(crate) fn lower_constant_expr(&mut self, term: &Term, origin: AstNodeId) -> Const {
        match term {
            Term::Lit(lit) => self.as_constant(*lit),
            // @@TirToConst: implement the conversion from an arbitrary TIR data term into a Const
            // value.
            _ => panic_on_span!(origin.span(), "cannot lower non-literal expression into constant"),
        }
    }

    /// Function that attempts to fold a constant operation. The function
    /// expects that the provided [Const]s are of integral kind i.e.
    /// `float`, `int`, or `char` and then tries to perform the operation on
    /// them. If the operation is not possible, then the function will
    /// return [None].
    pub(crate) fn try_fold_const_op(&mut self, op: BinOp, lhs: Const, rhs: Const) -> Option<Const> {
        if let Const::Int(interned_lhs) = lhs && let Const::Int(interned_rhs) = rhs
        {
            let lhs_const = interned_lhs.value();
            let rhs_const = interned_rhs.value();

            // First we need to coerce the types into the same primitive integer type, we do this
            // by checking the `suffix` and then coercing both ints into that value
            fold_int_const(op, lhs_const, rhs_const)
        }

        // Check if these two operands are floating point numbers
        else if let Const::Float(interned_lhs) = lhs && let Const::Float(interned_rhs) = rhs {
            let lhs_const = interned_lhs.value();
            let rhs_const = interned_rhs.value();

            match (lhs_const.value, rhs_const.value) {
                (FloatConstantValue::F32(lhs), FloatConstantValue::F32(rhs)) => fold_float_const(op, lhs, rhs),
                (FloatConstantValue::F64(lhs), FloatConstantValue::F64(rhs)) => fold_float_const(op, lhs, rhs),
                _ => unreachable!(),
            }
        } else {
            None
        }
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
        BinOp::Gt => return Some(Const::Bool(lhs > rhs)),
        BinOp::GtEq => return Some(Const::Bool(lhs >= rhs)),
        BinOp::Lt => return Some(Const::Bool(lhs < rhs)),
        BinOp::LtEq => return Some(Const::Bool(lhs <= rhs)),
        BinOp::Eq => return Some(Const::Bool(lhs == rhs)),
        BinOp::Neq => return Some(Const::Bool(lhs != rhs)),
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
    };

    value.map(|val| {
        // Create the new constant value and return it as a `const`
        let value: IntConstant = val.into();
        Const::Int(value.into())
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
        BinOp::Gt => return Some(Const::Bool(lhs > rhs)),
        BinOp::GtEq => return Some(Const::Bool(lhs >= rhs)),
        BinOp::Lt => return Some(Const::Bool(lhs < rhs)),
        BinOp::LtEq => return Some(Const::Bool(lhs <= rhs)),
        BinOp::Eq => return Some(Const::Bool(lhs == rhs)),
        BinOp::Neq => return Some(Const::Bool(lhs != rhs)),
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
        Const::Float(InternedFloat::create(value))
    })
}
