use dashmap::DashMap;

use hash_alloc::{collections::string::BrickString, Castle, Wall};
use hash_utils::counter;
use lazy_static::lazy_static;
use parking_lot::Mutex;

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

impl Default for IdentifierMap {
    fn default() -> Self {
        Self::new()
    }
}

impl IdentifierMap {
    pub fn new() -> Self {
        IdentifierMap {
            identifiers: DashMap::new(),
            reverse_lookup: DashMap::new(),
        }
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
