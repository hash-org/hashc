//! Various operators and functions defined that can be evaluated
//! by the constant evaluator.

use std::fmt;

use hash_repr::ty::{ReprTyId, COMMON_REPR_TYS};
use num_enum::{IntoPrimitive, TryFromPrimitive};

#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum UnOp {
    /// '-'
    Neg,
    /// '!'
    Not,
    /// '~'
    BitNot,
}

/// Represents a binary operation that is short-circuiting. These
/// operations are only valid on boolean values.
#[derive(Debug, PartialEq, Eq, Clone, Copy, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum LogicalBinOp {
    /// '||'
    Or,
    /// '&&'
    And,
}

/// Binary operations on [RValue]s that are typed as primitive, or have
/// `intrinsic` implementations defined for them. Any time that does not
/// implement these binary operations by default will create a function
/// call to the implementation of the binary operation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum BinOp {
    /// '=='
    Eq,
    /// '!='
    Neq,
    /// '|'
    BitOr,
    /// '&'
    BitAnd,
    /// '^'
    BitXor,
    /// '^^'
    Exp,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
    /// '>>'
    Shr,
    /// '<<'
    Shl,
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
    /// '%'
    Mod,
}

impl BinOp {
    /// Returns whether the [BinOp] can be "checked".
    pub fn is_checkable(&self) -> bool {
        matches!(self, Self::Add | Self::Sub | Self::Mul | Self::Shl | Self::Shr)
    }

    /// Check if the [BinOp] is a comparator.
    pub fn is_comparator(&self) -> bool {
        matches!(self, Self::Eq | Self::Neq | Self::Gt | Self::GtEq | Self::Lt | Self::LtEq)
    }

    /// Compute the type of [BinOp] operator when applied to
    /// a particular [ReprTy].
    pub fn ty(&self, lhs: ReprTyId, rhs: ReprTyId) -> ReprTyId {
        match self {
            BinOp::BitOr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::Div
            | BinOp::Sub
            | BinOp::Mod
            | BinOp::Add
            | BinOp::Mul
            | BinOp::Exp => {
                // Both `lhs` and `rhs` should be of the same type...
                debug_assert_eq!(
                    lhs, rhs,
                    "binary op types for `{:?}` should be equal, but got: lhs: `{}`, rhs: `{}`",
                    self, lhs, rhs
                );
                lhs
            }

            // Always the `lhs`, but `lhs` and `rhs` can be different types.
            BinOp::Shr | BinOp::Shl => lhs,

            // Comparisons
            BinOp::Eq | BinOp::Neq | BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq => {
                COMMON_REPR_TYS.bool
            }
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Eq => write!(f, "=="),
            BinOp::Neq => write!(f, "!="),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitXor => write!(f, "^"),
            BinOp::Exp => write!(f, "**"),
            BinOp::Gt => write!(f, ">"),
            BinOp::GtEq => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::LtEq => write!(f, "<="),
            BinOp::Shr => write!(f, ">>"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
        }
    }
}
