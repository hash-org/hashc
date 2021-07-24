//! Hash Compiler language keyword definitions
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;
use std::slice::Iter;

pub enum Keyword {
    Let,
    For,
    While,
    Loop,
    If,
    Else,
    Match,
    As,
    In,
    Where,
    Trait,
    Enum,
    Struct,
    Continue,
    Break,
    Return,
}

impl Keyword {
    pub fn iterator() -> Iter<'static, Keyword> {
        #[rustfmt::skip]
        static DIRECTIONS: [Keyword; 16] = [
            Keyword::Let, Keyword::For, Keyword::While, Keyword::Loop,
            Keyword::If, Keyword::Else, Keyword::Match, Keyword::As,
            Keyword::In, Keyword::Where, Keyword::Trait, Keyword::Enum,
            Keyword::Struct, Keyword::Continue, Keyword::Break, Keyword::Return,
        ];
        DIRECTIONS.iter()
    }

    pub fn to_str(&self) -> &str {
        match self {
            Keyword::As => "as",
            Keyword::In => "in",
            Keyword::Let => "let",
            Keyword::Match => "match",
            Keyword::For => "for",
            Keyword::While => "while",
            Keyword::Loop => "loop",
            Keyword::If => "if",
            Keyword::Else => "else",
            Keyword::Where => "where",
            Keyword::Trait => "trait",
            Keyword::Enum => "enum",
            Keyword::Struct => "struct",
            Keyword::Continue => "continue",
            Keyword::Break => "break",
            Keyword::Return => "return",
        }
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
