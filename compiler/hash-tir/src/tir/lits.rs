//! Contains structures related to literals, like numbers, strings, etc.
use std::{fmt::Display, ops::Deref};

use hash_ast::ast;
use hash_ast_utils::lit::{parse_float_const_from_lit, parse_int_const_from_lit, LitParseResult};
use hash_const_eval::Const;
use hash_storage::store::statics::StoreId;
use hash_target::{
    primitives::{FloatTy, IntTy},
    HasTarget,
};

use crate::{stores::tir_stores, tir_node_single_store};

// #[derive(Copy, Clone, Debug)]
// pub enum LitValue<R, V> {
//     Raw(R),
//     Value(V),
// }

// impl<R, V: Copy> LitValue<R, V> {
//     pub fn value(&self) -> V {
//         match self {
//             LitValue::Raw(_) => panic!("raw literal has not been baked"),
//             LitValue::Value(value) => *value,
//         }
//     }
// }

// /// An integer literal.
// ///
// /// Uses the `ast` representation.
// #[derive(Copy, Clone, Debug)]
// pub struct IntLit {
//     pub value: LitValue<ast::IntLit, Const<TyId>>,
// }

// impl IntLit {
//     /// Get the interned value of the literal.
//     pub fn value(&self) -> Const<TyId> {
//         self.value.value()
//     }

//     /// Check whether that value is negative.
//     ///
//     /// **Note**: For raw values, we just check if the value starts with a
// `-`.     pub fn is_negative(&self) -> bool {
//         match self.value {
//             LitValue::Raw(lit) => lit.hunk.span().map_contents(|s|
// s.starts_with('-')),             LitValue::Value(value) =>
// value.is_negative(),         }
//     }

//     /// Compute the [FloatTy] from the given float literal. The rules of
//     /// computation are as follows:
//     ///
//     /// - If the literal is unbaked, then we try to read the suffix on the
// type.     ///
//     /// - If the literal has a value, then we read the type of the value.
//     pub fn kind(&self) -> Option<IntTy> {
//         match self.value {
//             LitValue::Raw(lit) => match lit.kind {
//                 IntLitKind::Unsuffixed => None,
//                 IntLitKind::Suffixed(ty) => Some(ty),
//             },
//             LitValue::Value(value) => Some(value.ty()),
//         }
//     }

//     /// Check if the literal has been interned.
//     pub fn has_value(&self) -> bool {
//         matches!(self.value, LitValue::Value(_))
//     }
// }

// impl From<ast::IntLit> for Lit {
//     fn from(value: ast::IntLit) -> Self {
//         Lit::Int(value)
//     }
// }

// impl From<ast::ByteLit> for IntLit {
//     fn from(value: ast::ByteLit) -> Self {
//         let value: Scalar = value.data.into();
//         Self { value: LitValue::Value(Const::new(ConstKind::Scalar(value),
// TyId::U8)) }     }
// }

// /// A float literal.
// ///
// /// Uses the `ast` representation.
// #[derive(Copy, Clone, Debug)]
// pub struct FloatLit {
//     pub value: LitValue<ast::FloatLit, Const<TyId>>,
// }

// impl FloatLit {
//     /// Get the interned value of the literal.
//     pub fn constant(&self) -> Const<TyId> {
//         self.value.value()
//     }

//     /// Return the value of the float literal.
//     pub fn value(&self) -> f64 {
//         self.value.value().value().as_f64()
//     }

//     /// Compute the [FloatTy] from the given float literal. The rules of
//     /// computation are as follows:
//     ///
//     /// - If the literal is unbaked, then we try to read the suffix on the
// type.     ///
//     /// - If the literal has a value, then we read the type of the value.
//     pub fn kind(&self) -> Option<FloatTy> {
//         match self.value {
//             LitValue::Raw(lit) => match lit.kind {
//                 FloatLitKind::Unsuffixed => None,
//                 FloatLitKind::Suffixed(ty) => Some(ty),
//             },
//             LitValue::Value(value) => Some(value.ty()),
//         }
//     }

//     /// Check if the literal has been interned.
//     pub fn has_value(&self) -> bool {
//         matches!(self.value, LitValue::Value(_))
//     }

//     /// Bakes the float literal into a known representation.
//     ///
//     /// This function does not do anyttihng if the literal has already been
//     /// baked.
//     pub fn bake(&mut self, float_ty: FloatTy) -> LitParseResult<()> {
//         if let LitValue::Raw(lit) = self.value {
//             let value = parse_float_const_from_lit(&lit, Some(float_ty))?;

//             self.value = LitValue::Value(value);
//         }

//         Ok(())
//     }
// }

/// A literal
#[derive(Copy, Clone, Debug)]
pub enum Lit {
    /// An integer literal that is unbaked, it will require conversion into a
    /// [`Lit::Const`].
    Int(ast::IntLit),
    /// A float literal that is unbaked, it will require conversion into a
    /// [`Lit::Const`].
    Float(ast::FloatLit),

    /// A constant value that has been either baked or directly written.
    Const(Const),
}

tir_node_single_store!(Lit);

impl Lit {
    /// Bakes the integer literal into a known representation.
    ///
    /// This function does not do anything if the literal has already been
    /// baked.
    ///
    /// @@Future: we shouldn't change the literal in-place, we should return a
    /// new literal value, or we should return a new term which is the bigint
    /// term.
    pub fn bake_int<E: HasTarget>(&mut self, env: &E, int_ty: IntTy) -> LitParseResult<()> {
        if let Lit::Int(lit) = self {
            let value =
                parse_int_const_from_lit(&lit, Some(int_ty), env.target().ptr_size(), true)?;

            // @@AddBigIntsToPrelude: we just need to create a new alloc for the bigint.
            *self = Lit::Const(value);
        }

        Ok(())
    }

    /// Bakes the float literal into a known representation.
    ///
    /// This function does not do anyttihng if the literal has already been
    /// baked.
    pub fn bake_float(&mut self, float_ty: FloatTy) -> LitParseResult<()> {
        if let Lit::Float(lit) = self {
            let value = parse_float_const_from_lit(&lit, Some(float_ty))?;
            *self = Lit::Const(value);
        }

        Ok(())
    }
}

/// A literal pattern
///
/// This is a literal that can appear in a pattern, which does not include
/// floats.
#[derive(Copy, Clone, Debug)]
pub struct LitPat(pub LitId);

impl Deref for LitPat {
    type Target = LitId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for LitPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self.0.value() {
            // It's often the case that users don't include the range of the entire
            // integer and so we will write `-2147483648..x` and
            // same for max, what we want to do is write `MIN`
            // and `MAX` for these situations since it is easier for the
            // user to understand the problem.
            Lit::Int(_) | Lit::Float(_) => {
                write!(f, "<raw>")
            }
            Lit::Const(_value) => {
                // @@Cowbunga
                // let kind = value.map(|constant| constant.ty());

                // // ##Hack: we don't use size since it is never invoked because of
                // // integer constant don't store usize values.
                // let dummy_size = Size::ZERO;
                // let value = value.map(|constant| constant.value.as_u128());

                // if kind.numeric_min(dummy_size) == value {
                //     write!(f, "{kind}::MIN")
                // } else if kind.numeric_max(dummy_size) == value {
                //     write!(f, "{kind}::MAX")
                // } else {
                //     write!(f, "{lit}")
                // }
                todo!()
            }
        }
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lit::Int(_) | Lit::Float(_) => write!(f, "<raw>"),
            Lit::Const(_constant) => {
                // @@Cowbunga: Determine how to print the item based on the
                // type of the constant, we should have paths for integrals,
                // floats, and strings.
                todo!()
            }
        }
    }
}

impl Display for LitId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.value())
    }
}
