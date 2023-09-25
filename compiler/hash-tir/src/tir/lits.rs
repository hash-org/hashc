//! Contains structures related to literals, like numbers, strings, etc.
use std::{fmt::Display, ops::Deref};

use hash_ast::{
    ast,
    lit::{
        parse_float_const_from_lit, parse_int_const_from_lit, FloatLitKind, IntLitKind, IntValue,
        LitParseResult,
    },
};
use hash_source::constant::{IntConstant, InternedFloat, InternedInt, InternedStr};
use hash_storage::store::statics::StoreId;
use hash_target::{
    primitives::{FloatTy, IntTy},
    size::Size,
    HasTarget,
};

use crate::{stores::tir_stores, tir_node_single_store};

#[derive(Copy, Clone, Debug)]
pub enum LitValue<R, V> {
    Raw(R),
    Value(V),
}

impl<R, V: Copy> LitValue<R, V> {
    pub fn value(&self) -> V {
        match self {
            LitValue::Raw(_) => panic!("raw literal has not been baked"),
            LitValue::Value(value) => *value,
        }
    }
}

/// An integer literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct IntLit {
    pub value: LitValue<ast::IntLit, InternedInt>,
}

impl IntLit {
    /// Get the interned value of the literal.
    pub fn interned_value(&self) -> InternedInt {
        self.value.value()
    }

    /// Return the value of the integer literal.
    pub fn value(&self) -> IntConstant {
        self.value.value().value()
    }

    /// Check whether that value is negative.
    ///
    /// **Note**: For raw values, we just check if the value starts with a `-`.
    pub fn is_negative(&self) -> bool {
        match self.value {
            LitValue::Raw(lit) => lit.hunk.span().map_contents(|s| s.starts_with('-')),
            LitValue::Value(value) => value.is_negative(),
        }
    }

    /// Compute the [FloatTy] from the given float literal. The rules of
    /// computation are as follows:
    ///
    /// - If the literal is unbaked, then we try to read the suffix on the type.
    ///
    /// - If the literal has a value, then we read the type of the value.
    pub fn kind(&self) -> Option<IntTy> {
        match self.value {
            LitValue::Raw(lit) => match lit.kind {
                IntLitKind::Unsuffixed => None,
                IntLitKind::Suffixed(ty) => Some(ty),
            },
            LitValue::Value(value) => Some(value.ty()),
        }
    }

    /// Check if the literal has been interned.
    pub fn has_value(&self) -> bool {
        matches!(self.value, LitValue::Value(_))
    }

    /// Bakes the integer literal into a known representation.
    ///
    /// This function does not do anything if the literal has already been
    /// baked.
    ///
    /// @@Future: we shouldn't change the literal in-place, we should return a
    /// new literal value, or we should return a new term which is the bigint
    /// term.
    pub fn bake<E: HasTarget>(&mut self, env: &E, int_ty: IntTy) -> LitParseResult<()> {
        if let LitValue::Raw(lit) = self.value {
            let value =
                parse_int_const_from_lit(&lit, Some(int_ty), env.target().ptr_size(), true)?;

            match value {
                IntValue::Small(value) => {
                    self.value = LitValue::Value(value);
                }
                IntValue::Big(_) => {
                    // @@AddBigIntsToPrelude
                    unimplemented!()
                }
            }
        }

        Ok(())
    }
}

impl From<InternedInt> for IntLit {
    fn from(value: InternedInt) -> Self {
        Self { value: LitValue::Value(value) }
    }
}

impl From<ast::IntLit> for IntLit {
    fn from(value: ast::IntLit) -> Self {
        Self { value: LitValue::Raw(value) }
    }
}

/// A string literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct StrLit {
    pub underlying: ast::StrLit,
}

impl StrLit {
    /// Get the interned value of the literal.
    pub fn interned_value(&self) -> InternedStr {
        self.underlying.data
    }

    /// Return the value of the string literal.
    pub fn value(&self) -> &'static str {
        self.underlying.data.value()
    }
}

impl From<InternedStr> for StrLit {
    fn from(value: InternedStr) -> Self {
        Self { underlying: ast::StrLit { data: value } }
    }
}

impl From<ast::StrLit> for StrLit {
    fn from(value: ast::StrLit) -> Self {
        Self { underlying: value }
    }
}

/// A float literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct FloatLit {
    pub value: LitValue<ast::FloatLit, InternedFloat>,
}

impl FloatLit {
    /// Get the interned value of the literal.
    pub fn interned_value(&self) -> InternedFloat {
        self.value.value()
    }

    /// Return the value of the float literal.
    pub fn value(&self) -> f64 {
        self.value.value().value().as_f64()
    }

    /// Compute the [FloatTy] from the given float literal. The rules of
    /// computation are as follows:
    ///
    /// - If the literal is unbaked, then we try to read the suffix on the type.
    ///
    /// - If the literal has a value, then we read the type of the value.
    pub fn kind(&self) -> Option<FloatTy> {
        match self.value {
            LitValue::Raw(lit) => match lit.kind {
                FloatLitKind::Unsuffixed => None,
                FloatLitKind::Suffixed(ty) => Some(ty),
            },
            LitValue::Value(value) => Some(value.ty()),
        }
    }

    /// Check if the literal has been interned.
    pub fn has_value(&self) -> bool {
        matches!(self.value, LitValue::Value(_))
    }

    /// Bakes the float literal into a known representation.
    ///
    /// This function does not do anyttihng if the literal has already been
    /// baked.
    pub fn bake(&mut self, float_ty: FloatTy) -> LitParseResult<()> {
        if let LitValue::Raw(lit) = self.value {
            let value = parse_float_const_from_lit(&lit, Some(float_ty))?;

            self.value = LitValue::Value(value);
        }

        Ok(())
    }
}

impl From<InternedFloat> for FloatLit {
    fn from(value: InternedFloat) -> Self {
        Self { value: LitValue::Value(value) }
    }
}

impl From<ast::FloatLit> for FloatLit {
    fn from(value: ast::FloatLit) -> Self {
        Self { value: LitValue::Raw(value) }
    }
}

/// A character literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct CharLit {
    pub underlying: ast::CharLit,
}

impl CharLit {
    /// Return the value of the character literal.
    pub fn value(&self) -> char {
        self.underlying.data
    }
}

impl From<char> for CharLit {
    fn from(data: char) -> Self {
        Self { underlying: ast::CharLit { data } }
    }
}

impl From<ast::CharLit> for CharLit {
    fn from(value: ast::CharLit) -> Self {
        Self { underlying: value }
    }
}

/// A literal
#[derive(Copy, Clone, Debug)]
pub enum Lit {
    Int(IntLit),
    Str(StrLit),
    Char(CharLit),
    Float(FloatLit),
}

tir_node_single_store!(Lit);

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

impl Display for IntLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            LitValue::Raw(_) => write!(f, "<raw>"),
            LitValue::Value(value) => write!(f, "{value}"),
        }
    }
}

impl Display for FloatLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            LitValue::Raw(_) => write!(f, "<raw>"),
            LitValue::Value(value) => write!(f, "{value}"),
        }
    }
}

impl Display for StrLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.underlying.data)
    }
}

impl Display for CharLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.underlying.data)
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
            Lit::Int(lit) => {
                match lit.value {
                    LitValue::Raw(_) => {
                        // Defer to display impl for `Lit` below.
                        write!(f, "{lit}")
                    }
                    LitValue::Value(value) => {
                        let kind = value.map(|constant| constant.ty());

                        // ##Hack: we don't use size since it is never invoked because of
                        // integer constant don't store usize values.
                        let dummy_size = Size::ZERO;
                        let value = value.map(|constant| constant.value.as_u128());

                        if kind.numeric_min(dummy_size) == value {
                            write!(f, "{kind}::MIN")
                        } else if kind.numeric_max(dummy_size) == value {
                            write!(f, "{kind}::MAX")
                        } else {
                            write!(f, "{lit}")
                        }
                    }
                }
            }
            Lit::Str(lit) => write!(f, "{lit}"),
            Lit::Char(lit) => write!(f, "{lit}"),
            _ => unreachable!(),
        }
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lit::Int(lit) => write!(f, "{lit}"),
            Lit::Str(lit) => write!(f, "{lit}"),
            Lit::Char(lit) => write!(f, "{lit}"),
            Lit::Float(lit) => write!(f, "{lit}"),
        }
    }
}
