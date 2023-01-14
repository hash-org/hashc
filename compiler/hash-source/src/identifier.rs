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
        f.debug_tuple("Identifier")
            .field(&IDENTIFIER_MAP.get_ident(*self).to_owned())
            .field(&self.0)
            .finish()
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

impl From<usize> for Identifier {
    fn from(id: usize) -> Self {
        IDENTIFIER_MAP.create_ident(id.to_string().as_str())
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
}

/// Struct representing a globally accessible identifier map. The struct
/// contains a identifier map and another map for reverse lookups.
#[derive(Debug, Default)]
pub struct IdentifierMap<'c> {
    reverse_identifiers: DashMap<&'c str, Identifier, FnvBuildHasher>,
    identifiers: DashMap<Identifier, &'c str, FnvBuildHasher>,
}

impl<'c> IdentifierMap<'c> {
    /// Function to create a new identifier map instance.
    pub fn new() -> Self {
        IdentifierMap { reverse_identifiers: DashMap::default(), identifiers: DashMap::default() }
    }

    /// Function to create an identifier in the identifier map.
    pub fn create_ident(&self, ident_str: &str) -> Identifier {
        if let Some(ident) = self.reverse_identifiers.get(ident_str) {
            *ident
        } else {
            IDENTIFIER_STORAGE_WALL.with(|wall| {
                // We need to copy over the string so that it can be inserted into
                // the table
                let ident_str_alloc = BrickString::new(ident_str, wall).into_str();
                *self.reverse_identifiers.entry(ident_str_alloc).or_insert_with(|| {
                    let ident = Identifier::new();
                    self.identifiers.insert(ident, ident_str_alloc);
                    ident
                })
            })
        }
    }

    /// Function to lookup an identifier by an [Identifier] value in the
    /// identifier map.
    pub fn get_ident(&self, ident: Identifier) -> &'c str {
        self.identifiers.get(&ident).unwrap().value()
    }

    pub fn get_path(&self, path: impl Iterator<Item = impl Borrow<Identifier>>) -> String {
        path.map(|ident| self.get_ident(*ident.borrow())).collect::<Vec<&'_ str>>().join("::")
    }
}

macro_rules! core_idents {
    ($($name:ident ($value: expr)),* $(,)?) => {
        #[allow(non_camel_case_types, non_snake_case)]
        pub struct idents_generated {
             $(pub $name: Identifier, )*
        }

        impl idents_generated {
            pub fn from_ident_map(ident_map: &IdentifierMap) -> Self {
                Self {
                    $($name: ident_map.create_ident($value), )*
                }
            }
        }

        // @@Future: when lazy_static actually fixes the problem with idents, we can use lower
        // case `idents`
        lazy_static! {
            #[allow(non_upper_case_globals)]
            pub static ref IDENTS: idents_generated = idents_generated::from_ident_map(&IDENTIFIER_MAP);
        }
    };
}

// Prefill the `IdentifierMap` with commonly used/accessed identifiers.
core_idents! {
    a("a"),
    AnyType("AnyType"),
    b("b"),
    bool("bool"),
    char("char"),
    eq("eq"),
    Eq("Eq"),
    f32("f32"),
    f64("f64"),
    hash("hash"),
    Hash("Hash"),
    i128("i128"),
    i16("i16"),
    i32("i32"),
    i64("i64"),
    i8("i8"),
    ibig("ibig"),
    Index("index"),
    index("Index"),
    isize("isize"),
    K("K"),
    List("List"),
    Map("Map"),
    never("never"),
    Output("Output"),
    r#false("false"),
    r#true("true"),
    RawRef("RawRef"),
    RawRefMut("RawRefMut"),
    Ref("Ref"),
    RefMut("RefMut"),
    self_i("self"),
    Self_i("Self"),
    Set("Set"),
    str("str"),
    T("T"),
    trt_add_eq("add_eq"),
    trt_add("add"),
    trt_and("and"),
    trt_bit_and_eq("bit_and_eq"),
    trt_bit_and("bit_and"),
    trt_bit_exp_eq("bit_exp_eq"),
    trt_bit_exp("bit_exp"),
    trt_bit_or_eq("bit_or_eq"),
    trt_bit_or("bit_or"),
    trt_bit_xor_eq("bit_xor_eq"),
    trt_bit_xor("bit_xor"),
    trt_div_eq("div_eq"),
    trt_div("div"),
    trt_eq("eq"),
    trt_gt_eq("trt_gt_eq"),
    trt_gt("trt_gt"),
    trt_lt_eq("trt_lt_eq"),
    trt_lt("trt_lt"),
    trt_mod_eq("mod_eq"),
    trt_mod("mod"),
    trt_mul_eq("mul_eq"),
    trt_mul("mul"),
    trt_neq("neq"),
    trt_or("or"),
    trt_ord("ord"),
    trt_shl_eq("shl_eq"),
    trt_shl("shl"),
    trt_shr_eq("shr_eq"),
    trt_shr("shr"),
    trt_sub_eq("sub_eq"),
    trt_sub("sub"),
    Type("Type"),
    u128("u128"),
    u16("u16"),
    u32("u32"),
    u64("u64"),
    u8("u8"),
    ubig("ubig"),
    underscore("_"),
    usize("usize"),
    V("V"),
    value("value"),
    void("void"),

    // Directives that are pre-defined within the language.
    dump_ast("dump_ast"),
    dump_ir("dump_ir"),
    layout_of("layout_of"),
    intrinsics("intrinsics"),
}
