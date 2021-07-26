//! Hash Compiler language keyword definitions
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;
use strum_macros::{AsRefStr, EnumString, EnumVariantNames};

#[derive(Debug, PartialEq, AsRefStr, EnumString, EnumVariantNames)]
#[strum(serialize_all = "snake_case")]
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

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}
