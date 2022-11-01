//! Contains structures related to literals, like numbers, strings, etc.
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
