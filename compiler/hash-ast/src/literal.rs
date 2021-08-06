use hash_utils::counter;
use lazy_static::lazy_static;

use dashmap::DashMap;

/// A map containing identifiers that essentially point to a string literal that has been parsed
/// during the tokenisation process. This is so that we don't have to unecessarilly allocate a string
/// multiple times even if it occurs within the source.
#[derive(Debug, Default)]
pub struct StringLiteralMap {
    string_table: DashMap<StringLiteral, &'static str>,
    reverse_table: DashMap<&'static str, StringLiteral>,
}

counter! {
    name: StringLiteral,
    counter_name: STRING_LITERAL_COUNTER,
    visibility: pub,
    method_visibility:,
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
