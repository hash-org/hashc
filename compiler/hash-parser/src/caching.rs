use hash_utils::counter;
use lazy_static::lazy_static;

use dashmap::DashMap;

use hash_ast::ast::AstString;

/// A map containing identifiers that essentially point to a string literal that has been parsed
/// during the tokenisation process. This is so that we don't have to unecessarilly allocate a string
/// multiple times even if it occurs within the source.
#[derive(Debug, Default)]
pub struct StringLiteralMap {
    string_data: DashMap<StringIdentifier, AstString>,
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
        let ident = StringIdentifier::new();
        self.string_data.insert(ident, value);
        ident
    }

    /// Get the [String] behind the [StringIdentifier]
    pub fn lookup(&self, ident: StringIdentifier) -> String {
        self.string_data.get(&ident).unwrap().value().to_string()
    }
}
