//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{
    fmt::{self, Display},
    ops::Neg,
};

use dashmap::DashMap;
use fnv::FnvBuildHasher;
use hash_utils::counter;
use lazy_static::lazy_static;
use num_bigint::BigInt;

use crate::identifier::{Identifier, IDENTS};

/// The type of the float the [FloatLit] is storing.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatTy {
    F32,
    F64,
}

impl Display for FloatTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FloatTy::F32 => write!(f, "f32"),
            FloatTy::F64 => write!(f, "f64"),
        }
    }
}

/// The inner stored value of a [FloatConstant].
#[derive(Debug, Clone, Copy)]
pub enum FloatConstantValue {
    F64(f64),
    F32(f32),
}

impl Display for FloatConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FloatConstantValue::F64(inner) => write!(f, "{inner}"),
            FloatConstantValue::F32(inner) => write!(f, "{inner}"),
        }
    }
}

/// Interned float constant which stores the value of the float, and
/// an optional `type ascription` which is a suffix on the literal
/// describing which float kind it is, either being `f32` or `f64`.
#[derive(Debug, Clone, Copy)]
pub struct FloatConstant {
    /// Raw value of the float
    pub value: FloatConstantValue,
    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32.4f64`
    pub suffix: Option<Identifier>,
}

impl FloatConstant {
    /// Perform a negation operation on the [FloatConstant].
    pub fn negate(self) -> Self {
        let value = match self.value {
            FloatConstantValue::F64(inner) => FloatConstantValue::F64(-inner),
            FloatConstantValue::F32(inner) => FloatConstantValue::F32(-inner),
        };

        Self { value, suffix: self.suffix }
    }
}

counter! {
    name: InternedFloat,
    counter_name: INTERNED_FLOAT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl Display for FloatConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)?;

        if let Some(suffix) = self.suffix {
            write!(f, "{suffix}")?;
        }

        Ok(())
    }
}

impl Display for InternedFloat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_float_constant(*self))
    }
}

/// Unsigned integer type variants.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UIntTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    USize,
    UBig,
}

impl UIntTy {
    /// Get the size of [IntTy] in bytes. Returns [None] for
    /// [UIntTy::UBig] variants
    pub const fn size(&self, ptr_width: usize) -> Option<u64> {
        match self {
            UIntTy::U8 => Some(1),
            UIntTy::U16 => Some(2),
            UIntTy::U32 => Some(4),
            UIntTy::U64 => Some(8),
            UIntTy::USize => Some(ptr_width as u64),
            UIntTy::U128 => Some(16),
            UIntTy::UBig => None,
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            UIntTy::U8 => Some(BigInt::from(u8::MAX)),
            UIntTy::U16 => Some(BigInt::from(u16::MAX)),
            UIntTy::U32 => Some(BigInt::from(u32::MAX)),
            UIntTy::U64 => Some(BigInt::from(u64::MAX)),
            UIntTy::U128 => Some(BigInt::from(u128::MAX)),
            UIntTy::USize => {
                let max = !0u64 >> (64 - (ptr_width * 8));
                Some(BigInt::from(max))
            }
            UIntTy::UBig => None,
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type.
    pub fn min(&self) -> BigInt {
        0.into()
    }

    /// Convert the [UIntTy] into a primitive type name
    pub fn to_name(&self) -> &'static str {
        match self {
            UIntTy::U8 => "u8",
            UIntTy::U16 => "u16",
            UIntTy::U32 => "u32",
            UIntTy::U64 => "u64",
            UIntTy::U128 => "u128",
            UIntTy::USize => "usize",
            UIntTy::UBig => "ubig",
        }
    }
}

impl Display for UIntTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// Signed integer type variants.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SIntTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    ISize,
    IBig,
}

impl SIntTy {
    /// Get the size of [IntTy] in bytes. Returns [None] for
    /// [UIntTy::UBig] variants
    pub const fn size(&self, ptr_width: usize) -> Option<u64> {
        match self {
            SIntTy::I8 => Some(1),
            SIntTy::I16 => Some(2),
            SIntTy::I32 => Some(4),
            SIntTy::I64 => Some(8),
            SIntTy::ISize => Some(ptr_width as u64),
            SIntTy::I128 => Some(16),
            SIntTy::IBig => None,
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            SIntTy::I8 => Some(BigInt::from(i8::MAX)),
            SIntTy::I16 => Some(BigInt::from(i16::MAX)),
            SIntTy::I32 => Some(BigInt::from(i32::MAX)),
            SIntTy::I64 => Some(BigInt::from(i64::MAX)),
            SIntTy::I128 => Some(BigInt::from(i128::MAX)),
            SIntTy::ISize => {
                // convert the size to a signed integer
                let max = (1u64 << (ptr_width * 8 - 1)) - 1;
                Some(BigInt::from(max))
            }
            SIntTy::IBig => None,
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined minimum and so the
    /// function returns [None].
    pub fn min(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            SIntTy::I8 => Some(BigInt::from(i8::MIN)),
            SIntTy::I16 => Some(BigInt::from(i16::MIN)),
            SIntTy::I32 => Some(BigInt::from(i32::MIN)),
            SIntTy::I64 => Some(BigInt::from(i64::MIN)),
            SIntTy::I128 => Some(BigInt::from(i128::MIN)),
            SIntTy::ISize => {
                let min = (i64::MAX) << ((ptr_width * 8) - 1);
                Some(BigInt::from(min))
            }
            SIntTy::IBig => None,
        }
    }

    /// Convert the [IntTy] into a primitive type name
    pub fn to_name(&self) -> &'static str {
        match self {
            SIntTy::I8 => "i8",
            SIntTy::I16 => "i16",
            SIntTy::I32 => "i32",
            SIntTy::I64 => "i64",
            SIntTy::I128 => "i128",
            SIntTy::ISize => "isize",
            SIntTy::IBig => "ibig",
        }
    }
}

impl Display for SIntTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// The representation of an integer type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntTy {
    /// Signed integer variant.
    Int(SIntTy),
    /// Unsigned integer variant.
    UInt(UIntTy),
}

impl IntTy {
    /// Convert the type into a name.
    pub fn to_name(&self) -> &'static str {
        match self {
            IntTy::Int(ty) => ty.to_name(),
            IntTy::UInt(ty) => ty.to_name(),
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            IntTy::Int(ty) => ty.max(ptr_width),
            IntTy::UInt(ty) => ty.max(ptr_width),
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type. For sizes `ibig` there is no defined minimum and so the
    /// function returns [None].
    pub fn min(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            IntTy::Int(ty) => ty.min(ptr_width),
            IntTy::UInt(ty) => Some(ty.min()),
        }
    }

    /// Function to get the size of the integer type in bytes.
    pub fn size(&self, ptr_width: usize) -> Option<u64> {
        match self {
            IntTy::Int(ty) => ty.size(ptr_width),
            IntTy::UInt(ty) => ty.size(ptr_width),
        }
    }

    /// Check if the type is signed.
    pub fn is_signed(&self) -> bool {
        matches!(self, IntTy::Int(_))
    }

    /// Check if the type is a pointer integral type, i.e. `isize` or `usize`.
    pub fn is_ptr_sized_integral(self) -> bool {
        matches!(self, IntTy::Int(SIntTy::ISize) | IntTy::UInt(UIntTy::USize))
    }

    /// Check if the type is a [BigInt] variant, i.e. `ibig` or `ubig`.
    pub fn is_big_sized_integral(self) -> bool {
        matches!(self, IntTy::Int(SIntTy::IBig) | IntTy::UInt(UIntTy::UBig))
    }
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// Value of the [IntConstant], this kind be either the `inlined`
/// variant where we just fallback to using `u64` for small sized
/// integer constants, and then in the unlikely scenario of needing
/// more than a [u64] to represent the constant, we will then
/// fallback to [BigInt].
#[derive(Debug, Eq, PartialEq, Hash)]
pub enum IntConstantValue {
    /// For small values, we store inline
    Small([u8; 8]),
    /// For bigger values, we just store a pointer to the `BigInt`
    Big(Box<BigInt>),
}

impl From<BigInt> for IntConstantValue {
    fn from(value: BigInt) -> Self {
        let bits = value.bits();

        // We want to see if we can fit this big-int in a `u128` so we can just copy it
        // directly
        if bits <= 64 {
            let data = (<BigInt as TryInto<i64>>::try_into(value).unwrap()).to_be_bytes();
            IntConstantValue::Small(data)
        } else {
            IntConstantValue::Big(Box::new(value))
        }
    }
}

/// Interned literal constant which stores the raw value of the
/// integer and an optional `type ascription` which binds the
/// defined literal value to some ascribed type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct IntConstant {
    /// Raw value of the integer. This is stored as either a `u128` which can be
    /// directly stored as the value which happens in `99%` of cases, if the
    /// constant is not big enough to store this integer, then we resort to
    /// using [IntConstant
    value: IntConstantValue,
    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32u64`
    pub suffix: Option<Identifier>,
}

impl IntConstant {
    /// Convert the constant into a Big endian order byte stream.
    pub fn to_bytes_be(&self) -> Vec<u8> {
        match &self.value {
            IntConstantValue::Small(value) => value.to_vec(),
            IntConstantValue::Big(value) => value.to_signed_bytes_be(),
        }
    }

    /// Convert the constant into a [BigInt].
    pub fn to_big_int(self) -> BigInt {
        match self.value {
            IntConstantValue::Small(inner) => BigInt::from_signed_bytes_be(&inner),
            IntConstantValue::Big(inner) => *inner,
        }
    }

    /// Check if the [IntConstant] is `signed` by checking if the specified
    /// suffix matches one of the available signed integer suffixes. If no
    /// suffix is specified, the assumed type of the integer constant is `i32`
    /// and therefore this follows the same assumption.
    pub fn is_signed(&self) -> bool {
        match self.suffix {
            Some(suffix) => match suffix {
                i if IDENTS.i8 == i => true,
                i if IDENTS.i16 == i => true,
                i if IDENTS.i32 == i => true,
                i if IDENTS.i64 == i => true,
                i if IDENTS.i128 == i => true,
                i if IDENTS.isize == i => true,
                i if IDENTS.ibig == i => true,
                _ => false,
            },
            None => true,
        }
    }

    /// Negate the [IntConstant] provided that the constant is signed. If
    /// the constant is not signed, then no negation operation is applied.
    pub fn negate(self) -> Self {
        // Do nothing if this constant is not signed.
        if !self.is_signed() {
            return self;
        }

        let value = match self.value {
            IntConstantValue::Small(inner) => {
                // Flip the sign, and the convert back to `be` bytes
                let value = -i64::from_be_bytes(inner);
                IntConstantValue::Small(value.to_be_bytes())
            }
            IntConstantValue::Big(inner) => IntConstantValue::Big(Box::new(inner.neg())),
        };

        Self { value, suffix: self.suffix }
    }
}

counter! {
    name: InternedInt,
    counter_name: INTERNED_INT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl Display for IntConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            // We want to snip the value from the `total` value since we don't care about the
            // rest...
            IntConstantValue::Small(value) => {
                if self.is_signed() {
                    write!(f, "{}", i64::from_be_bytes(*value))?;
                } else {
                    write!(f, "{}", u64::from_be_bytes(*value))?;
                }
            }
            IntConstantValue::Big(value) => write!(f, "{value}")?,
        }

        if let Some(suffix) = self.suffix {
            write!(f, "{suffix}")?;
        }

        Ok(())
    }
}

impl Display for InternedInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_int_constant(*self))
    }
}

counter! {
    name: InternedStr,
    counter_name: STR_LIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl Display for InternedStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_string(*self))
    }
}

// Utility methods for converting from a InternedString to an InternedStrLit and
// vice versa.

impl From<&str> for InternedStr {
    fn from(string: &str) -> Self {
        CONSTANT_MAP.create_string(string)
    }
}

impl From<String> for InternedStr {
    fn from(string: String) -> Self {
        CONSTANT_MAP.create_string(&string)
    }
}

impl From<InternedStr> for &str {
    fn from(string: InternedStr) -> Self {
        CONSTANT_MAP.lookup_string(string)
    }
}

impl From<InternedStr> for String {
    fn from(string: InternedStr) -> Self {
        String::from(CONSTANT_MAP.lookup_string(string))
    }
}

/// A map containing identifiers that essentially point to a string literal that
/// has been parsed during the tokenisation process. This is so that we don't
/// have to unnecessarily allocate a string multiple times even if it occurs
/// within the source.
#[derive(Debug, Default)]
pub struct ConstantMap {
    /// Where the interned strings are stored.
    string_table: DashMap<InternedStr, &'static str, FnvBuildHasher>,

    /// It's useful to lookup [InternedStr] from a raw string.
    reverse_string_table: DashMap<&'static str, InternedStr, FnvBuildHasher>,

    /// Float literals store
    float_table: DashMap<InternedFloat, FloatConstant, FnvBuildHasher>,

    /// Integer literal store, `char` constants are not stored here
    int_table: DashMap<InternedInt, IntConstant, FnvBuildHasher>,
}

lazy_static! {
    pub static ref CONSTANT_MAP: ConstantMap = ConstantMap::default();
}

impl ConstantMap {
    /// Add a new string to the map, this will add an additional entry even if
    /// the string is already within the map.
    pub fn create_string(&self, value: &str) -> InternedStr {
        if let Some(key) = self.reverse_string_table.get(value) {
            *key
        } else {
            // @@Memory: memory leaks could be avoided/masked by having a wall?
            // copy over the string so that we can insert it into the reverse lookup table
            let value_copy = Box::leak(value.to_owned().into_boxed_str());
            *self.reverse_string_table.entry(value_copy).or_insert_with(|| {
                let interned = InternedStr::new();
                self.string_table.insert(interned, value_copy);
                interned
            })
        }
    }

    /// Get the [String] behind the [InternedStr]
    pub fn lookup_string(&self, ident: InternedStr) -> &'static str {
        self.string_table.get(&ident).unwrap().value()
    }

    /// Create a `f64` [FloatConstant] within the [ConstantMap]
    pub fn create_f64_float_constant(
        &self,
        value: f64,
        suffix: Option<Identifier>,
    ) -> InternedFloat {
        let ident = InternedFloat::new();
        let constant = FloatConstant { value: FloatConstantValue::F64(value), suffix };

        self.float_table.insert(ident, constant);
        ident
    }

    /// Create a `f32` [FloatConstant] within the [ConstantMap]
    pub fn create_f32_float_constant(
        &self,
        value: f32,
        suffix: Option<Identifier>,
    ) -> InternedFloat {
        let ident = InternedFloat::new();
        let constant = FloatConstant { value: FloatConstantValue::F32(value), suffix };

        self.float_table.insert(ident, constant);
        ident
    }

    /// Get the [FloatConstant] behind the [InternedFloat]
    pub fn lookup_float_constant(&self, id: InternedFloat) -> FloatConstant {
        *self.float_table.get(&id).unwrap().value()
    }

    /// Perform a negation operation on an [InternedFloat].
    pub fn negate_float_constant(&self, id: InternedFloat) {
        self.float_table.alter(&id, |_, value| value.negate());
    }

    /// Create a [IntConstant] within the [ConstantMap].
    pub fn create_int_constant(&self, value: BigInt, suffix: Option<Identifier>) -> InternedInt {
        let value = IntConstantValue::from(value);

        let ident = InternedInt::new();
        let constant = IntConstant { value, suffix };

        // Insert the entries into the map and the reverse-lookup map
        self.int_table.insert(ident, constant);

        ident
    }

    /// Get the [IntConstant] behind the [InternedInt]
    pub fn lookup_int_constant(&self, id: InternedInt) -> IntConstant {
        let lookup_value = self.int_table.get(&id).unwrap();
        let IntConstant { value, suffix } = lookup_value.value();

        let value = match value {
            IntConstantValue::Small(inner) => IntConstantValue::Small(*inner),
            IntConstantValue::Big(inner) => IntConstantValue::Big(inner.clone()),
        };

        IntConstant { value, suffix: *suffix }
    }

    /// Perform a negation operation on an [InternedInt].
    ///
    /// N.B: This function has no effect on the stored constant if it is not
    /// signed.
    pub fn negate_int_constant(&self, id: InternedInt) {
        self.int_table.alter(&id, |_, value| value.negate());
    }
}
