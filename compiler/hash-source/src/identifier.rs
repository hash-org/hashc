//! Hash AST identifier storage utilities and wrappers.
use std::{
    borrow::{Borrow, Cow},
    fmt::{Debug, Display},
    thread_local,
};

use dashmap::DashMap;
use fnv::FnvBuildHasher;
use hash_alloc::{collections::string::BrickString, Castle, Wall};
use hash_utils::counter;
use lazy_static::lazy_static;

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

/// Holds some default identifiers in order to avoid map lookups.
#[allow(non_snake_case)]
pub struct CoreIdentifiers {
    pub underscore: Identifier,
    pub intrinsics: Identifier,

    // TC:
    pub i8: Identifier,
    pub i16: Identifier,
    pub i32: Identifier,
    pub i64: Identifier,
    pub isize: Identifier,
    pub u8: Identifier,
    pub u16: Identifier,
    pub u32: Identifier,
    pub u64: Identifier,
    pub usize: Identifier,
    pub f32: Identifier,
    pub f64: Identifier,
    pub str: Identifier,
    pub char: Identifier,
    pub bool: Identifier,
    pub r#true: Identifier,
    pub r#false: Identifier,
    pub AnyType: Identifier,
    pub Type: Identifier,
    pub never: Identifier,
    pub void: Identifier,
    pub T: Identifier,
    pub Ref: Identifier,
    pub RefMut: Identifier,
    pub RawRef: Identifier,
    pub RawRefMut: Identifier,
    pub Hash: Identifier,
    pub Eq: Identifier,
    pub List: Identifier,
    pub Set: Identifier,
    pub Map: Identifier,
    pub Index: Identifier,
    pub Self_i: Identifier,
    pub self_i: Identifier,
    pub Output: Identifier,
    pub index: Identifier,
    pub hash: Identifier,
    pub value: Identifier,
    pub eq: Identifier,
    pub a: Identifier,
    pub b: Identifier,
    pub K: Identifier,
    pub V: Identifier,
}

impl CoreIdentifiers {
    /// Create the core identifiers inside the given [IdentifierMap].
    pub fn from_ident_map(ident_map: &IdentifierMap) -> Self {
        Self {
            underscore: ident_map.create_ident("_"),
            intrinsics: ident_map.create_ident("intrinsics"),
            i8: ident_map.create_ident("i8"),
            i16: ident_map.create_ident("i16"),
            i32: ident_map.create_ident("i32"),
            i64: ident_map.create_ident("i64"),
            u8: ident_map.create_ident("u8"),
            u16: ident_map.create_ident("u16"),
            u32: ident_map.create_ident("u32"),
            u64: ident_map.create_ident("u64"),
            f32: ident_map.create_ident("f32"),
            f64: ident_map.create_ident("f64"),
            str: ident_map.create_ident("str"),
            char: ident_map.create_ident("char"),
            bool: ident_map.create_ident("bool"),
            r#true: ident_map.create_ident("true"),
            r#false: ident_map.create_ident("false"),
            AnyType: ident_map.create_ident("AnyType"),
            Type: ident_map.create_ident("Type"),
            never: ident_map.create_ident("never"),
            void: ident_map.create_ident("void"),
            T: ident_map.create_ident("T"),
            Ref: ident_map.create_ident("Ref"),
            RefMut: ident_map.create_ident("RefMut"),
            RawRef: ident_map.create_ident("RawRef"),
            RawRefMut: ident_map.create_ident("RawRefMut"),
            Hash: ident_map.create_ident("Hash"),
            Eq: ident_map.create_ident("Eq"),
            List: ident_map.create_ident("List"),
            Set: ident_map.create_ident("Set"),
            Map: ident_map.create_ident("Map"),
            Index: ident_map.create_ident("Index"),
            Self_i: ident_map.create_ident("Self"),
            self_i: ident_map.create_ident("self"),
            Output: ident_map.create_ident("Output"),
            index: ident_map.create_ident("index"),
            hash: ident_map.create_ident("hash"),
            value: ident_map.create_ident("value"),
            K: ident_map.create_ident("K"),
            V: ident_map.create_ident("V"),
            eq: ident_map.create_ident("eq"),
            a: ident_map.create_ident("a"),
            b: ident_map.create_ident("b"),
            isize: ident_map.create_ident("isize"),
            usize: ident_map.create_ident("usize"),
        }
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
