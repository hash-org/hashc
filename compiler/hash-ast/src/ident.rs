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


/// Struct representing a globally accessible identifier map. The struct contains a identifier
/// map and another map for reverse lookups.
#[derive(Debug, Default)]
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

impl IdentifierMap {
    /// Function to create a new identifier map instance.
    pub fn new() -> Self {
        IdentifierMap {
            identifiers: DashMap::new(),
            reverse_lookup: DashMap::new(),
        }
    }

    /// Create an identifier in the identifier map but check if the it exists before trying
    /// to insert the value into the map and just return it otherwise.
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

    /// Create the identifier in the identifiers map but also allocate the static string in a provided
    /// [Wall].
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

    /// Function to create an identifier in the identifier map.
    pub fn create_ident(&self, ident_str: &str) -> Identifier {
        let wall = IDENTIFIER_STORAGE_WALL.lock();
        self.create_ident_in(ident_str, &wall)
    }

    /// Function to lookup an identifier by an [Identifier] value in the identifier map.
    pub fn ident_name(&self, ident: Identifier) -> &'static str {
        self.reverse_lookup.get(&ident).unwrap().value()
    }
}
