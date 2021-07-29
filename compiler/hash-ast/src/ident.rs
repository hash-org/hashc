use crate::{ast::AstString, keyword::Keyword};
use dashmap::DashMap;
use hash_utils::counter;
use lazy_static::lazy_static;
use strum::VariantNames;

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct IdentifierMap {
    identifiers: DashMap<AstString, Identifier>,
    reverse_lookup: DashMap<Identifier, AstString>,
}

lazy_static! {
    pub static ref IDENTIFIER_MAP: IdentifierMap = IdentifierMap::default();
}

// Ensure that keywords have exact identifier values...
// static_assertions::const_assert_eq!(*IDENTIFIER_MAP.ident_data.get("let").unwrap(), Identifier::from(Keyword::Let as u32));

impl IdentifierMap {
    pub fn default() -> Self {
        let map = IdentifierMap {
            identifiers: DashMap::new(),
            reverse_lookup: DashMap::new(),
        };

        // Initialise the identifier map with all the keywords that are reserved in the language
        // so that it will be easier to perform comparisons on when a keyword is present, rather than
        // always looking them up. This means that the names of each keyword is guaranteed to have a
        // identifier value in the ranges of 0...15
        for keyword in Keyword::VARIANTS {
            map.create_ident(AstString::Borrowed(keyword));
        }

        // assert_eq!(map.ident_name(Identifier::from(0)), "let".to_string());
        // assert_eq!(map.ident_name(Identifier::from(14)), "break".to_string());

        map
    }

    pub fn create_ident(&self, ident_str: AstString) -> Identifier {
        if let Some(key) = self.identifiers.get(&ident_str) {
            *key
        } else {
            let ident = Identifier::new();
            let copy = ident_str.clone();

            self.identifiers.insert(ident_str, ident);
            self.reverse_lookup.insert(ident, copy);
            ident
        }
    }

    pub fn ident_name(&self, ident: Identifier) -> String {
        self.reverse_lookup.get(&ident).unwrap().value().to_string()
    }
}
