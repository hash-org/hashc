use crate::keyword::Keyword;
use dashmap::DashMap;

use hash_alloc::{collections::string::BrickString, Castle, Wall};
use hash_utils::counter;
use lazy_static::lazy_static;
use parking_lot::Mutex;
use strum::VariantNames;

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct IdentifierMap {
    identifiers: DashMap<&'static str, Identifier>,
    reverse_lookup: DashMap<Identifier, &'static str>,
}

lazy_static! {
    static ref IDENTIFIER_STORAGE_CASTLE: Castle = Castle::new();
    static ref IDENTIFIER_STORAGE_WALL: Mutex<Wall<'static>> =
        Mutex::new(IDENTIFIER_STORAGE_CASTLE.wall());
}

lazy_static! {
    pub static ref IDENTIFIER_MAP: IdentifierMap = IdentifierMap::new();
}

// Ensure that keywords have exact identifier values...
// static_assertions::const_assert_eq!(*IDENTIFIER_MAP.ident_data.get("let").unwrap(), Identifier::from(Keyword::Let as u32));

impl Default for IdentifierMap {
    fn default() -> Self {
        Self::new()
    }
}

impl IdentifierMap {
    pub fn new() -> Self {
        let map = IdentifierMap {
            identifiers: DashMap::new(),
            reverse_lookup: DashMap::new(),
        };

        let wall = IDENTIFIER_STORAGE_WALL.lock();

        // Initialise the identifier map with all the keywords that are reserved in the language
        // so that it will be easier to perform comparisons on when a keyword is present, rather than
        // always looking them up. This means that the names of each keyword is guaranteed to have a
        // identifier value in the ranges of 0...15
        for &keyword in Keyword::VARIANTS {
            // let value = BrickString::new(keyword, &wall);
            // map.create_ident(value);
            map.create_ident_in(keyword, &wall);
        }

        // assert_eq!(map.ident_name(Identifier::from(0)), "let".to_string());
        // assert_eq!(map.ident_name(Identifier::from(14)), "break".to_string());

        map
    }

    pub fn create_ident_existing(&self, ident_str: &'static str) -> Identifier {
        if let Some(key) = self.identifiers.get(ident_str) {
            *key
        } else {
            let ident = Identifier::new();

            self.identifiers.insert(ident_str, ident);
            self.reverse_lookup.insert(ident, ident_str);
            ident
        }
    }

    fn create_ident_in(&self, ident_str: &str, wall: &Wall<'static>) -> Identifier {
        if let Some(key) = self.identifiers.get(ident_str) {
            *key
        } else {
            let ident = Identifier::new();
            let ident_str_alloc = BrickString::new(ident_str, wall).into_str();

            self.identifiers.insert(ident_str_alloc, ident);
            self.reverse_lookup.insert(ident, ident_str_alloc);
            ident
        }
    }

    pub fn create_ident(&self, ident_str: &str) -> Identifier {
        let wall = IDENTIFIER_STORAGE_WALL.lock();
        self.create_ident_in(ident_str, &wall)
    }

    pub fn ident_name(&self, ident: Identifier) -> &'static str {
        self.reverse_lookup.get(&ident).unwrap().value()
    }
}
