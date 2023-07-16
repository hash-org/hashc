//! Contains structures related to literals, like numbers, strings, etc.
use std::fmt::Display;

use hash_ast::ast;
use hash_source::constant::{InternedFloat, InternedInt, InternedStr, CONSTANT_MAP};
use hash_target::size::Size;
use num_bigint::BigInt;

/// An integer literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct IntLit {
    pub underlying: ast::IntLit,
}

impl IntLit {
    /// Create a new [IntLit] from an [InternedInt].
    pub fn from_value(value: InternedInt) -> Self {
        Self { underlying: ast::IntLit { value, kind: ast::IntLitKind::Unsuffixed } }
    }

    /// Get the interned value of the literal.
    pub fn interned_value(&self) -> InternedInt {
        self.underlying.value
    }

    /// Return the value of the integer literal.
    pub fn value(&self) -> BigInt {
        (&CONSTANT_MAP.lookup_int(self.underlying.value)).try_into().unwrap()
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
        CONSTANT_MAP.lookup_string(self.underlying.data)
    }
}

impl From<InternedStr> for StrLit {
    fn from(value: InternedStr) -> Self {
        Self { underlying: ast::StrLit { data: value } }
    }
}

/// A float literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct FloatLit {
    pub underlying: ast::FloatLit,
}

impl FloatLit {
    /// Get the interned value of the literal.
    pub fn interned_value(&self) -> InternedFloat {
        self.underlying.value
    }

    /// Return the value of the float literal.
    pub fn value(&self) -> f64 {
        CONSTANT_MAP.lookup_float(self.underlying.value).as_f64()
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
    /// Create a new [CharLit] from a literal character value.
    pub fn from_literal(data: char) -> Self {
        Self { underlying: ast::CharLit { data } }
    }

    /// Return the value of the character literal.
    pub fn value(&self) -> char {
        self.underlying.data
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

/// A literal pattern
///
/// This is a literal that can appear in a pattern, which does not include
/// floats.
#[derive(Copy, Clone, Debug)]
pub enum LitPat {
    Int(IntLit),
    Str(StrLit),
    Char(CharLit),
}

impl From<LitPat> for Lit {
    fn from(val: LitPat) -> Self {
        match val {
            LitPat::Int(l) => Lit::Int(l),
            LitPat::Str(l) => Lit::Str(l),
            LitPat::Char(l) => Lit::Char(l),
        }
    }
}

impl Display for IntLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.underlying.value)
    }
}

impl Display for StrLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", CONSTANT_MAP.lookup_string(self.underlying.data))
    }
}

impl Display for CharLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.underlying.data)
    }
}

impl Display for FloatLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.underlying.value)
    }
}

impl Display for LitPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // It's often the case that users don't include the range of the entire
            // integer and so we will write `-2147483648..x` and
            // same for max, what we want to do is write `MIN`
            // and `MAX` for these situations since it is easier for the
            // user to understand the problem.
            LitPat::Int(lit) => {
                let (kind, value): (_, BigInt) = CONSTANT_MAP
                    .map_int(lit.interned_value(), |constant| {
                        (constant.ty(), constant.value.as_big())
                    });

                // @@Hack: we don't use size since it is never invoked because of
                // integer constant don't store usize values.
                let dummy_size = Size::ZERO;

                if let Some(min) = kind.min(dummy_size) && min == value {
                    write!(f, "{kind}::MIN")
                } else if let Some(max) = kind.max(dummy_size) && max == value {
                    write!(f, "{kind}::MAX")
                } else {
                    write!(f, "{lit}")
                }
            }
            LitPat::Str(lit) => write!(f, "{lit}"),
            LitPat::Char(lit) => write!(f, "{lit}"),
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
