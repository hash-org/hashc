//! Hash AST string literal storage utilities and wrappers.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use std::fmt::Display;

use fnv::FnvBuildHasher;
use hash_utils::counter;
use lazy_static::lazy_static;

use dashmap::DashMap;

/// A map containing identifiers that essentially point to a string literal that has been parsed
/// during the tokenisation process. This is so that we don't have to unnecessarily allocate a string
/// multiple times even if it occurs within the source.
#[derive(Debug, Default)]
pub struct StringLiteralMap {
    string_table: DashMap<StringLiteral, &'static str, FnvBuildHasher>,
    reverse_table: DashMap<&'static str, StringLiteral, FnvBuildHasher>,
}

counter! {
    name: StringLiteral,
    counter_name: STRING_LITERAL_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl Display for StringLiteral {
    /// Render the identifier when displaying it
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", STRING_LITERAL_MAP.lookup(*self))
    }
}

impl From<&str> for StringLiteral {
    /// Create an identifier from a string.
    fn from(string: &str) -> Self {
        STRING_LITERAL_MAP.create_string(string)
    }
}

impl From<String> for StringLiteral {
    /// Create an identifier from a string.
    fn from(string: String) -> Self {
        STRING_LITERAL_MAP.create_string(&string)
    }
}

impl From<StringLiteral> for &str {
    /// Convert an identifier into a string, panics if the identifier doesn't exist.
    fn from(string: StringLiteral) -> Self {
        STRING_LITERAL_MAP.lookup(string)
    }
}

impl From<StringLiteral> for String {
    /// Convert an identifier into a string, panics if the identifier doesn't exist.
    fn from(string: StringLiteral) -> Self {
        String::from(STRING_LITERAL_MAP.lookup(string))
    }
}

lazy_static! {
    pub static ref STRING_LITERAL_MAP: StringLiteralMap = StringLiteralMap::default();
}

impl StringLiteralMap {
    /// Add a new string to the map, this will add an additional entry even if the string is already
    /// within the map.
    pub fn create_string(&self, value: &str) -> StringLiteral {
        if let Some(key) = self.reverse_table.get(value) {
            *key
        } else {
            let ident = StringLiteral::new();

            // copy over the string so that we can insert it into the reverse lookup table
            // let wall = STATIC_CASTLE.wall();
            // let value_copy = BrickString::new(value, &wall);
            let value_copy = Box::leak(value.to_owned().into_boxed_str());

            self.reverse_table.insert(value_copy, ident);
            self.string_table.insert(ident, value_copy);
            ident
        }
    }

    /// Get the [String] behind the [StringLiteral]
    pub fn lookup(&self, ident: StringLiteral) -> &'static str {
        self.string_table.get(&ident).unwrap().value()
    }
}
