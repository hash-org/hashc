//! Hash Compiler token keyword definitions
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::fmt;
use strum_macros::AsRefStr;

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
}

/// Enum Variants for keywords

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}
