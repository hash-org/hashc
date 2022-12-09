//! Contains structures related to literals, like numbers, strings, etc.
use std::fmt::Display;

use hash_ast::ast;

/// An integer literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct IntLit {
    pub underlying: ast::IntLit,
}

/// A string literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct StrLit {
    pub underlying: ast::StrLit,
}

/// A float literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct FloatLit {
    pub underlying: ast::FloatLit,
}

/// A character literal.
///
/// Uses the `ast` representation.
#[derive(Copy, Clone, Debug)]
pub struct CharLit {
    pub underlying: ast::CharLit,
}

/// A literal pattern
///
/// Floats are not valid patterns, so they are not included here.
#[derive(Copy, Clone, Debug)]
pub enum LitPat {
    Int(IntLit),
    Str(StrLit),
    Char(CharLit),
}

/// A literal term
#[derive(Copy, Clone, Debug)]
pub enum LitTerm {
    Int(IntLit),
    Str(StrLit),
    Char(CharLit),
    Float(FloatLit),
}

impl Display for IntLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.underlying.value, self.underlying.kind)
    }
}

impl Display for StrLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.underlying.data)
    }
}

impl Display for CharLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.underlying.data)
    }
}

impl Display for FloatLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.underlying.value, self.underlying.kind)
    }
}

impl Display for LitPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LitPat::Int(lit) => write!(f, "{lit}"),
            LitPat::Str(lit) => write!(f, "{lit}"),
            LitPat::Char(lit) => write!(f, "{lit}"),
        }
    }
}

impl Display for LitTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LitTerm::Int(lit) => write!(f, "{lit}"),
            LitTerm::Str(lit) => write!(f, "{lit}"),
            LitTerm::Char(lit) => write!(f, "{lit}"),
            LitTerm::Float(lit) => write!(f, "{lit}"),
        }
    }
}
