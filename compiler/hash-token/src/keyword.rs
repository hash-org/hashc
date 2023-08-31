//! Hash Compiler token keyword definitions.
use std::fmt;

use phf::phf_map;
use strum_macros::AsRefStr;

/// Enum Variants for keywords.
#[derive(Debug, Copy, Clone, PartialEq, Eq, AsRefStr)]
#[strum(serialize_all = "snake_case")]
pub enum Keyword {
    For,
    While,
    Loop,
    If,
    Else,
    Match,
    As,
    In,
    Trait,
    Enum,
    Struct,
    Continue,
    Break,
    Return,
    Import,
    Raw,
    False,
    True,
    Unsafe,
    Pub,
    Priv,
    Mut,
    Mod,
    Impl,
    Type,
    TypeOf,
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

/// A static map of keywords to their enum variants using a
/// perfect hashing function to quickly lookup the keyword.
///
/// @@Future: look into somehow using `gperf` instead?
static KEYWORDS: phf::Map<&'static str, Keyword> = phf_map! {
    "for" => Keyword::For,
    "while" => Keyword::While,
    "loop" => Keyword::Loop,
    "if" => Keyword::If,
    "else" => Keyword::Else,
    "match" => Keyword::Match,
    "as" => Keyword::As,
    "in" => Keyword::In,
    "trait" => Keyword::Trait,
    "enum" => Keyword::Enum,
    "struct" => Keyword::Struct,
    "continue" => Keyword::Continue,
    "break" => Keyword::Break,
    "return" => Keyword::Return,
    "import" => Keyword::Import,
    "raw" => Keyword::Raw,
    "false" => Keyword::False,
    "true" => Keyword::True,
    "unsafe" => Keyword::Unsafe,
    "pub" => Keyword::Pub,
    "priv" => Keyword::Priv,
    "mut" => Keyword::Mut,
    "mod" => Keyword::Mod,
    "impl" => Keyword::Impl,
    "type" => Keyword::Type,
    "typeof" => Keyword::TypeOf,
};

#[inline(always)]
pub fn ident_is_keyword(s: &str) -> Option<Keyword> {
    KEYWORDS.get(s).copied()
}
