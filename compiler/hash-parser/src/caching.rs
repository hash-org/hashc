use hash_utils::counter;
use lazy_static::lazy_static;

use dashmap::DashMap;

use hash_ast::ast::AstString;

/// A map containing identifiers that essentially point to a string literal that has been parsed
/// during the tokenisation process. This is so that we don't have to unecessarilly allocate a string
/// multiple times even if it occurs within the source.
#[derive(Debug, Default)]
pub struct StringLiteralMap {
    string_table: DashMap<StringIdentifier, AstString>,
    reverse_table: DashMap<AstString, StringIdentifier>,
}

counter! {
    name: StringIdentifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

lazy_static! {
    pub static ref STRING_LITERAL_MAP: StringLiteralMap = StringLiteralMap::default();
}

impl StringLiteralMap {
    /// Add a new string to the map, this will add an additional entry even if the string is already
    /// within the map.
    pub fn create_string(&self, value: AstString) -> StringIdentifier {
        if let Some(key) = self.reverse_table.get(&value) {
            *key
        } else {
            let ident = StringIdentifier::new();

            // copy over the string so that we can insert it into the reverse lookup table
            let value_copy = value.clone();

            self.reverse_table.insert(value, ident);
            self.string_table.insert(ident, value_copy);
            ident
        }
    }

    /// Get the [String] behind the [StringIdentifier]
    pub fn lookup(&self, ident: StringIdentifier) -> String {
        self.string_table.get(&ident).unwrap().value().to_string()
    }
}
