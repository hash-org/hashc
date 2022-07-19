//! Hash Compiler string literal storage utilities and wrappers.
use std::fmt::Display;

use fnv::FnvBuildHasher;
use hash_utils::counter;
use lazy_static::lazy_static;

use dashmap::DashMap;

/// A map containing identifiers that essentially point to a string literal that
/// has been parsed during the tokenisation process. This is so that we don't
/// have to unnecessarily allocate a string multiple times even if it occurs
/// within the source.
#[derive(Debug, Default)]
pub struct StrLitMap {
    string_table: DashMap<Str, &'static str, FnvBuildHasher>,
    reverse_table: DashMap<&'static str, Str, FnvBuildHasher>,
}

counter! {
    name: Str,
    counter_name: STR_LIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl Display for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", STR_LIT_MAP.lookup(*self))
    }
}

// Utility methods for converting from a String to an StrLit and vice
// versa.

impl From<&str> for Str {
    fn from(string: &str) -> Self {
        STR_LIT_MAP.create_string(string)
    }
}

impl From<String> for Str {
    fn from(string: String) -> Self {
        STR_LIT_MAP.create_string(&string)
    }
}

impl From<Str> for &str {
    fn from(string: Str) -> Self {
        STR_LIT_MAP.lookup(string)
    }
}

impl From<Str> for String {
    fn from(string: Str) -> Self {
        String::from(STR_LIT_MAP.lookup(string))
    }
}

lazy_static! {
    pub static ref STR_LIT_MAP: StrLitMap = StrLitMap::default();
}

impl StrLitMap {
    /// Add a new string to the map, this will add an additional entry even if
    /// the string is already within the map.
    pub fn create_string(&self, value: &str) -> Str {
        if let Some(key) = self.reverse_table.get(value) {
            *key
        } else {
            let ident = Str::new();

            // copy over the string so that we can insert it into the reverse lookup table
            let value_copy = Box::leak(value.to_owned().into_boxed_str());

            self.reverse_table.insert(value_copy, ident);
            self.string_table.insert(ident, value_copy);
            ident
        }
    }

    /// Get the [String] behind the [StrLit]
    pub fn lookup(&self, ident: Str) -> &'static str {
        self.string_table.get(&ident).unwrap().value()
    }
}
