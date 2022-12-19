//! Hash Compiler lexer utilities for identifiers and other character sequences.

/// True if `c` is valid as a first character of an identifier.
// @@Future: Support unicode within idents?
pub(crate) fn is_id_start(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c == '_'
}

/// True if `c` is valid as a non-first character of an identifier.
// @@Future: Support unicode within idents?
pub(crate) fn is_id_continue(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'
}
