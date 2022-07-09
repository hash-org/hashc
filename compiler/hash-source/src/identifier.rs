//! Hash AST identifier storage utilities and wrappers.
use dashmap::DashMap;

use fnv::FnvBuildHasher;
use hash_alloc::{collections::string::BrickString, Castle, Wall};
use hash_utils::counter;
use lazy_static::lazy_static;
use std::{
    borrow::{Borrow, Cow},
    fmt::{Debug, Display},
    thread_local,
};

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
    derives: (Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd),
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", IDENTIFIER_MAP.get_ident(*self))
    }
}

impl Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Identifier").field(&IDENTIFIER_MAP.get_ident(*self).to_owned()).finish()
    }
}

// Utility methods for converting from a String to an Identifier and vice versa.

impl From<&str> for Identifier {
    fn from(name: &str) -> Self {
        IDENTIFIER_MAP.create_ident(name)
    }
}

impl From<String> for Identifier {
    fn from(name: String) -> Self {
        IDENTIFIER_MAP.create_ident(name.as_str())
    }
}

impl From<Identifier> for &str {
    fn from(ident: Identifier) -> Self {
        IDENTIFIER_MAP.get_ident(ident)
    }
}

impl From<Identifier> for String {
    fn from(ident: Identifier) -> Self {
        String::from(IDENTIFIER_MAP.get_ident(ident))
    }
}

impl From<Identifier> for Cow<'static, str> {
    fn from(ident: Identifier) -> Self {
        Cow::from(IDENTIFIER_MAP.get_ident(ident))
    }
}

thread_local! {
    static IDENTIFIER_STORAGE_WALL: Wall<'static> = IDENTIFIER_STORAGE_CASTLE.wall();
}

lazy_static! {
    static ref IDENTIFIER_STORAGE_CASTLE: Castle = Castle::new();
    pub static ref IDENTIFIER_MAP: IdentifierMap<'static> = IdentifierMap::new();
    pub static ref CORE_IDENTIFIERS: CoreIdentifiers =
        CoreIdentifiers::from_ident_map(&IDENTIFIER_MAP);
}

/// Struct representing a globally accessible identifier map. The struct
/// contains a identifier map and another map for reverse lookups.
#[derive(Debug, Default)]
pub struct IdentifierMap<'c> {
    identifiers: DashMap<&'c str, Identifier, FnvBuildHasher>,
    reverse_lookup: DashMap<Identifier, &'c str, FnvBuildHasher>,
}

/// Holds some default identifiers in order to avoid map lookups when e.g.
/// generating the AST.
pub struct CoreIdentifiers {
    pub underscore: Identifier,
}

impl CoreIdentifiers {
    /// Create the core identifiers inside the given [IdentifierMap].
    pub fn from_ident_map(ident_map: &IdentifierMap) -> Self {
        Self { underscore: ident_map.create_ident("_") }
    }
}

impl<'c> IdentifierMap<'c> {
    /// Function to create a new identifier map instance.
    pub fn new() -> Self {
        IdentifierMap { identifiers: DashMap::default(), reverse_lookup: DashMap::default() }
    }

    /// Function to create an identifier in the identifier map.
    pub fn create_ident(&self, ident_str: &str) -> Identifier {
        if let Some(ident) = self.identifiers.get(ident_str) {
            *ident
        } else {
            IDENTIFIER_STORAGE_WALL.with(|wall| {
                let ident = Identifier::new();

                // We need to copy over the string so that it can be inserted into
                // the table
                let ident_str_alloc = BrickString::new(ident_str, wall).into_str();

                self.identifiers.insert(ident_str_alloc, ident);
                self.reverse_lookup.insert(ident, ident_str_alloc);
                ident
            })
        }
    }

    /// Function to lookup an identifier by an [Identifier] value in the
    /// identifier map.
    pub fn get_ident(&self, ident: Identifier) -> &'c str {
        self.reverse_lookup.get(&ident).unwrap().value()
    }

    pub fn get_path(&self, path: impl Iterator<Item = impl Borrow<Identifier>>) -> String {
        path.map(|ident| self.get_ident(*ident.borrow())).collect::<Vec<&'_ str>>().join("::")
    }
}
