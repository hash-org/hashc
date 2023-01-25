//! Contains structures related to literals, like numbers, strings, etc.
use std::fmt::{self, Display};

use hash_ast::ast;
use hash_source::constant::CONSTANT_MAP;
use hash_utils::store::SequenceStore;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    pats::{PatListId, Spread},
    terms::TermListId,
};

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

/// A list constructor
///
/// Contains a sequence of terms.
#[derive(Copy, Clone, Debug)]
pub struct ListCtor {
    pub elements: TermListId,
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

/// A primitive term
#[derive(Copy, Clone, Debug)]
pub enum PrimTerm {
    Lit(Lit),
    List(ListCtor),
}

/// A list pattern.
///
/// This is in the form `[x_1,...,x_n]`, with an optional spread `...(name?)` at
/// some position.
#[derive(Copy, Clone, Debug)]
pub struct ListPat {
    /// The sequence of patterns in the list pattern.
    pub pats: PatListId,
    /// The spread pattern, if any.
    pub spread: Option<Spread>,
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

impl Display for WithEnv<'_, &LitPat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            LitPat::Int(lit) => write!(f, "{lit}"),
            LitPat::Str(lit) => write!(f, "{lit}"),
            LitPat::Char(lit) => write!(f, "{lit}"),
        }
    }
}

impl fmt::Display for WithEnv<'_, &ListPat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        self.stores().pat_list().map_fast(self.value.pats, |pat_list| {
            let mut pat_args_formatted =
                pat_list.iter().map(|arg| self.env().with(*arg).to_string()).collect::<Vec<_>>();

            if let Some(spread) = self.value.spread {
                pat_args_formatted.insert(spread.index, self.env().with(spread).to_string());
            }

            for (i, pat_arg) in pat_args_formatted.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pat_arg}")?;
            }
            Ok(())
        })?;
        write!(f, "]")
    }
}

impl Display for WithEnv<'_, &ListCtor> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.env().with(self.value.elements))
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

impl Display for WithEnv<'_, &PrimTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            PrimTerm::Lit(lit) => write!(f, "{lit}"),
            PrimTerm::List(list_term) => write!(f, "{}", self.env().with(list_term)),
        }
    }
}
