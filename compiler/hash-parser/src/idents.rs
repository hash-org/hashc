//! Hash compiler lexer utilities for identifiers.
//!
//! All rights reserved 2021 (c) The Hash Language authors

/// True if `c` is valid as a first character of an identifier.
// @@ Future: Support unicode within idents?
pub fn is_id_start(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || c == '_'
}

/// True if `c` is valid as a non-first character of an identifier.
// @@ Future: Support unicode within idents?
pub fn is_id_continue(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || ('0'..='9').contains(&c) || c == '_'
}

/// The passed string is lexically an identifier.
pub fn is_ident(string: &str) -> bool {
    let mut chars = string.chars();
    if let Some(start) = chars.next() {
        is_id_start(start) && chars.all(is_id_continue)
    } else {
        false
    }
}

