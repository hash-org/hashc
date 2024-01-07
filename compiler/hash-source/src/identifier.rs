//! Hash AST identifier storage utilities and wrappers.
use std::{
    borrow::Cow,
    fmt::{Debug, Display},
    thread_local,
};

use hash_storage::{
    arena::{Castle, Wall},
    string::BrickString,
};
use hash_target::primitives::*;
use hash_utils::{
    counter, dashmap::DashMap, fnv::FnvBuildHasher, fxhash::FxBuildHasher,
    lazy_static::lazy_static, num_traits::PrimInt,
};

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
    derives: (Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd),
}

impl Identifier {
    /// Get the length of the identifier.
    pub fn len(&self) -> usize {
        IDENTIFIER_MAP.get_ident(*self).len()
    }

    /// Check whether the identifier is empty.
    ///
    /// Just to get Clippy to shut up!
    pub fn is_empty(&self) -> bool {
        IDENTIFIER_MAP.get_ident(*self).is_empty()
    }

    /// Get the identifier as a static string.
    pub fn as_str(&self) -> &'static str {
        IDENTIFIER_MAP.get_ident(*self)
    }

    /// Create an [Identifier] from a numeric type.
    ///
    /// This will convert the numeric using the [fmt::Display]
    /// implementation, and finally create a new identifier for
    /// it.
    pub fn num<N: PrimInt + ToString>(value: N) -> Self {
        IDENTIFIER_MAP.create_ident(value.to_string().as_str())
    }
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

impl From<UIntTy> for Identifier {
    fn from(value: UIntTy) -> Self {
        match value {
            UIntTy::U8 => IDENTS.u8,
            UIntTy::U16 => IDENTS.u16,
            UIntTy::U32 => IDENTS.u32,
            UIntTy::U64 => IDENTS.u64,
            UIntTy::U128 => IDENTS.u128,
            UIntTy::USize => IDENTS.usize,
        }
    }
}

impl From<SIntTy> for Identifier {
    fn from(value: SIntTy) -> Self {
        match value {
            SIntTy::I8 => IDENTS.i8,
            SIntTy::I16 => IDENTS.i16,
            SIntTy::I32 => IDENTS.i32,
            SIntTy::I64 => IDENTS.i64,
            SIntTy::I128 => IDENTS.i128,
            SIntTy::ISize => IDENTS.isize,
        }
    }
}

impl From<BigIntTy> for Identifier {
    fn from(value: BigIntTy) -> Self {
        match value {
            BigIntTy::IBig => IDENTS.ibig,
            BigIntTy::UBig => IDENTS.ubig,
        }
    }
}

impl From<IntTy> for Identifier {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::Int(ty) => ty.into(),
            IntTy::UInt(ty) => ty.into(),
            IntTy::Big(ty) => ty.into(),
        }
    }
}

impl TryFrom<Identifier> for IntTy {
    type Error = ();

    fn try_from(value: Identifier) -> Result<Self, Self::Error> {
        match value {
            i if i == IDENTS.i8 => Ok(IntTy::Int(SIntTy::I8)),
            i if i == IDENTS.i16 => Ok(IntTy::Int(SIntTy::I16)),
            i if i == IDENTS.i32 => Ok(IntTy::Int(SIntTy::I32)),
            i if i == IDENTS.i64 => Ok(IntTy::Int(SIntTy::I64)),
            i if i == IDENTS.i128 => Ok(IntTy::Int(SIntTy::I128)),
            i if i == IDENTS.isize => Ok(IntTy::Int(SIntTy::ISize)),
            i if i == IDENTS.u8 => Ok(IntTy::UInt(UIntTy::U8)),
            i if i == IDENTS.u16 => Ok(IntTy::UInt(UIntTy::U16)),
            i if i == IDENTS.u32 => Ok(IntTy::UInt(UIntTy::U32)),
            i if i == IDENTS.u64 => Ok(IntTy::UInt(UIntTy::U64)),
            i if i == IDENTS.u128 => Ok(IntTy::UInt(UIntTy::U128)),
            i if i == IDENTS.usize => Ok(IntTy::UInt(UIntTy::USize)),
            i if i == IDENTS.ibig => Ok(IntTy::Big(BigIntTy::IBig)),
            i if i == IDENTS.ubig => Ok(IntTy::Big(BigIntTy::UBig)),
            _ => Err(()),
        }
    }
}

impl TryFrom<Identifier> for FloatTy {
    type Error = ();

    fn try_from(value: Identifier) -> Result<Self, Self::Error> {
        match value {
            i if i == IDENTS.f32 => Ok(FloatTy::F32),
            i if i == IDENTS.f64 => Ok(FloatTy::F64),
            _ => Err(()),
        }
    }
}

impl From<FloatTy> for Identifier {
    fn from(value: FloatTy) -> Self {
        match value {
            FloatTy::F32 => IDENTS.f32,
            FloatTy::F64 => IDENTS.f64,
        }
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
    identifiers: DashMap<Identifier, &'c str, FxBuildHasher>,
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
}

macro_rules! core_idents {
    ($($name:ident : $value: expr),* $(,)?) => {
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
    // How long until we get the entire alphabet?
    a: "a",
    b: "b",

    AnyType: "AnyType",
    bool: "bool",
    char: "char",
    eq: "eq",
    Eq: "Eq",
    f32: "f32",
    f64: "f64",
    hash: "hash",
    Hash: "Hash",
    i128: "i128",
    i16: "i16",
    i32: "i32",
    i64: "i64",
    i8: "i8",
    ibig: "ibig",
    Index: "index",
    index: "Index",
    isize: "isize",
    K: "K",
    List: "List",
    Map: "Map",
    never: "never",
    Output: "Output",
    r#false: "false",
    r#true: "true",
    RawRef: "RawRef",
    RawRefMut: "RawRefMut",
    Ref: "Ref",
    RefMut: "RefMut",
    self_i: "self",
    Self_i: "Self",
    Set: "Set",
    str: "str",
    T: "T",
    trt_add_eq: "add_eq",
    trt_add: "add",
    trt_and: "and",
    trt_bit_and_eq: "bit_and_eq",
    trt_bit_and: "bit_and",
    trt_bit_exp_eq: "bit_exp_eq",
    trt_bit_exp: "bit_exp",
    trt_bit_or_eq: "bit_or_eq",
    trt_bit_or: "bit_or",
    trt_bit_xor_eq: "bit_xor_eq",
    trt_bit_xor: "bit_xor",
    trt_div_eq: "div_eq",
    trt_div: "div",
    trt_eq: "eq",
    trt_gt_eq: "trt_gt_eq",
    trt_gt: "trt_gt",
    trt_lt_eq: "trt_lt_eq",
    trt_lt: "trt_lt",
    trt_mod_eq: "mod_eq",
    trt_mod: "mod",
    trt_mul_eq: "mul_eq",
    trt_mul: "mul",
    trt_neq: "neq",
    trt_or: "or",
    trt_ord: "ord",
    trt_shl_eq: "shl_eq",
    trt_shl: "shl",
    trt_shr_eq: "shr_eq",
    trt_shr: "shr",
    trt_sub_eq: "sub_eq",
    trt_sub: "sub",
    Type: "Type",

    // The `main` function entry point.
    main: "main",

    u128: "u128",
    u16: "u16",
    u32: "u32",
    u64: "u64",
    u8: "u8",
    ubig: "ubig",
    underscore: "_",
    usize: "usize",
    V: "V",
    value: "value",
    void: "void",

    // Dumping AST/TIR/IR etc.
    dump_ast: "dump_ast",
    dump_ir: "dump_ir",
    dump_tir: "dump_tir",
    dump_llvm_ir: "dump_llvm_ir",

    // Language items
    lang: "lang",
    intrinsics: "intrinsics",
    entry_point: "entry_point",
    transmute: "transmute",
    cast: "cast",

    // Language attributes
    no_mangle: "no_mangle",
    foreign: "foreign",

    // Layout intrinsics
    repr: "repr",
    layout_of: "layout_of",

    // Function flags
    pure: "pure",

    // Running at compile time
    run: "run",

    // Intrinsic function item names
    sqrt_f32: "sqrtf32",
    sqrt_f64: "sqrtf64",
    powi_f32: "powif32",
    powi_f64: "powif64",
    sin_f32: "sinf32",
    sin_f64: "sinf64",
    cos_f32: "cosf32",
    cos_f64: "cosf64",
    pow_f32: "powf32",
    pow_f64: "powf64",
    exp_f32: "expf32",
    exp_f64: "expf64",
    exp2_f32: "exp2f32",
    exp2_f64: "exp2f64",
    log_f32: "logf32",
    log_f64: "logf64",
    log10_f32: "log10f32",
    log10_f64: "log10f64",
    log2_f32: "log2f32",
    log2_f64: "log2f64",
    fma_f32: "fmaf32",
    fma_f64: "fmaf64",
    fabs_f32: "fabsf32",
    fabs_f64: "fabsf64",
    memcmp: "memcmp",
}
