//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{cmp::Ordering, fmt, ops::Neg};

use dashmap::DashMap;
use fnv::FnvBuildHasher;
// Re-export the "primitives" from the hash-target crate so that everyone can use
// them who depends on `hash-source`
pub use hash_target::primitives::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_utils::counter;
use lazy_static::lazy_static;
use num_bigint::BigInt;

use crate::identifier::{Identifier, IDENTS};

/// The inner stored value of a [FloatConstant].
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum FloatConstantValue {
    F64(f64),
    F32(f32),
}

impl fmt::Display for FloatConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

    /// The type of the float constant,
    pub ty: FloatTy,

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

        Self { value, ty: self.ty, suffix: self.suffix }
    }
}

/// Provide implementations for converting primitive floating point types into
/// [FloatConstant]s.
macro_rules! float_const_impl_into {
    ($($ty:ident, $kind: ident);*) => {
        $(
            impl From<$ty> for FloatConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: FloatConstantValue::$kind(value),
                        ty: FloatTy::$kind,
                        suffix: Some(IDENTS.$ty),
                    }
                }
            }
        )*
    };
}

float_const_impl_into!(f32, F32; f64, F64);

counter! {
    name: InternedFloat,
    counter_name: INTERNED_FLOAT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl fmt::Display for FloatConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)?;

        if let Some(suffix) = self.suffix {
            write!(f, "_{suffix}")?;
        }

        Ok(())
    }
}

impl fmt::Display for InternedFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_float_constant(*self))
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
            UIntTy::UBig => IDENTS.ubig,
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
            SIntTy::IBig => IDENTS.ibig,
        }
    }
}

impl From<IntTy> for Identifier {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::Int(ty) => ty.into(),
            IntTy::UInt(ty) => ty.into(),
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
            i if i == IDENTS.ibig => Ok(IntTy::Int(SIntTy::IBig)),
            i if i == IDENTS.u8 => Ok(IntTy::UInt(UIntTy::U8)),
            i if i == IDENTS.u16 => Ok(IntTy::UInt(UIntTy::U16)),
            i if i == IDENTS.u32 => Ok(IntTy::UInt(UIntTy::U32)),
            i if i == IDENTS.u64 => Ok(IntTy::UInt(UIntTy::U64)),
            i if i == IDENTS.u128 => Ok(IntTy::UInt(UIntTy::U128)),
            i if i == IDENTS.usize => Ok(IntTy::UInt(UIntTy::USize)),
            i if i == IDENTS.ubig => Ok(IntTy::UInt(UIntTy::UBig)),
            _ => Err(()),
        }
    }
}

/// Value of the [IntConstant], this kind be either the `inlined`
/// variant where we just fallback to using `u64` for small sized
/// integer constants, and then in the unlikely scenario of needing
/// more than a [u128] to represent the constant, we will then
/// fallback to [BigInt].
///
/// N.B: Values are always stored and accessed in **Big Endian** format.
#[derive(Debug, Eq, PartialEq, Hash)]
pub enum IntConstantValue {
    /// For small values, we store inline
    Small([u8; 16]),
    /// For bigger values, we just store a pointer to the `BigInt`
    Big(Box<BigInt>),
}

impl IntConstantValue {
    /// Create a new [IntConstantValue] from little endian ordered bytes.
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= 16 {
            let mut arr = [0u8; 16];
            arr[..bytes.len()].copy_from_slice(bytes);

            // If the last byte is negative, we need to sign extend
            if bytes.last().map(|b| b & 0x80 != 0).unwrap_or(false) {
                for i in arr.iter_mut().skip(bytes.len()) {
                    *i = 0xff;
                }
            }

            // Then finally reverse
            arr.reverse();
            Self::Small(arr)
        } else {
            Self::Big(Box::new(BigInt::from_signed_bytes_le(bytes)))
        }
    }

    /// Create a new [IntConstantValue] from big endian ordered bytes
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        if bytes.len() <= 16 {
            let mut arr = [0u8; 16];
            arr[..bytes.len()].copy_from_slice(bytes);

            // If the last byte is negative, we need to sign extend
            // if bytes.last().map(|b| b & 0x80 != 0).unwrap_or(false) {
            //     for i in arr.iter_mut().skip(bytes.len()) {
            //         *i = 0xff;
            //     }
            // }

            Self::Small(arr)
        } else {
            Self::Big(Box::new(BigInt::from_signed_bytes_be(bytes)))
        }
    }
}

impl From<BigInt> for IntConstantValue {
    fn from(value: BigInt) -> Self {
        let bits = value.bits();

        // We want to see if we can fit this big-int in a `u128` so we can just copy it
        // directly
        if bits <= 128 {
            let data = (<BigInt as TryInto<i128>>::try_into(value).unwrap()).to_be_bytes();
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

    /// The type of the int constant that is stored.
    pub ty: IntTy,

    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32u64`
    pub suffix: Option<Identifier>,
}

impl IntConstant {
    /// Create a new [IntConstant] from a given `value` and `ty`.
    pub fn new(value: IntConstantValue, ty: IntTy, suffix: Option<Identifier>) -> Self {
        Self { value, ty, suffix }
    }

    /// Create a [IntConstant] from the a provided value and suffix, and then
    /// insert it into the [ConstantMap] returning the [InternedInt].
    pub fn from_big_int(value: BigInt, ty: IntTy, suffix: Option<Identifier>) -> Self {
        Self { value: IntConstantValue::from(value), ty, suffix }
    }

    pub fn from_uint(value: u128, ty: IntTy) -> Self {
        Self { value: IntConstantValue::from_be_bytes(&value.to_be_bytes()), ty, suffix: None }
    }

    /// Create a [IntConstant] from Little endian bytes and an [IntTy]. It is
    /// assumed that the correct amount of bytes are provided to this
    /// function.
    pub fn from_le_bytes(&self, bytes: &[u8], ty: IntTy) -> Self {
        IntConstant { value: IntConstantValue::from_le_bytes(bytes), ty, suffix: None }
    }

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
        self.ty.is_signed()
    }

    /// Check if the [IntConstant] is represented as the
    /// [IntConstantValue::Small], as in this is an integer type that is not
    /// represented using a `ibig` or `ubig` type.
    pub fn is_small(&self) -> bool {
        matches!(self.value, IntConstantValue::Small(_))
    }

    /// Assuming that the [IntConstant] is a represented as a
    /// [IntConstantValue::Small], then this function will read the bytes of
    /// this scalar int.
    pub fn get_bytes(&self) -> [u8; 16] {
        match &self.value {
            IntConstantValue::Small(value) => *value,
            _ => unreachable!(),
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
                // @@Todo: don't always assume that this is a 64 biy integer.

                // Flip the sign, and the convert back to `be` bytes
                let value = -i128::from_be_bytes(inner);
                IntConstantValue::Small(value.to_be_bytes())
            }
            IntConstantValue::Big(inner) => IntConstantValue::Big(Box::new(inner.neg())),
        };

        Self { value, ty: self.ty, suffix: self.suffix }
    }
}

impl PartialOrd for IntConstant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.ty, other.ty) {
            (IntTy::Int(left), IntTy::Int(right)) if left == right => {
                // We need to get the value from the constant, and then
                // perform a comparison on the two values.
                if self.is_small() && other.is_small() {
                    let left_val = i128::from_be_bytes(self.get_bytes());
                    let right_val = i128::from_be_bytes(other.get_bytes());

                    Some(left_val.cmp(&right_val))
                } else {
                    // Deal with bigints...
                    unimplemented!()
                }
            }
            (IntTy::UInt(left), IntTy::UInt(right)) if left == right => {
                if self.is_small() && other.is_small() {
                    let left_val = u128::from_be_bytes(self.get_bytes());
                    let right_val = u128::from_be_bytes(other.get_bytes());

                    Some(left_val.cmp(&right_val))
                } else {
                    // Deal with bigints...
                    unimplemented!()
                }
            }
            _ => None,
        }
    }
}

/// Provide implementations for converting primitive integer types into
/// [IntConstant]s.
macro_rules! int_const_impl_from {
    ($($ty:ident),*; $into: ty) => {
        $(
            impl From<$ty> for IntConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: IntConstantValue::Small((value as $into).to_be_bytes()),
                        // @@Hack: derive the type into the identifier, this is to
                        // avoid using a procedural macro to derive the type.
                        ty: (IDENTS.$ty).try_into().unwrap(),
                        suffix: Some(IDENTS.$ty)
                    }
                }
            }
        )*
    };
    () => {
    };
}

int_const_impl_from!(i8, i16, i32, i64, isize, i128; i128);
int_const_impl_from!(u8, u16, u32, u64, usize, u128; u128);

/// Provide implementations for converting [IntConstant]s into primitive
/// integer types. This uses the system defined sizes for the primitive
/// integer types, and should not be used to reliably convert into target
/// sized integers.
macro_rules! int_const_impl_into {
    ($($ty:ident),*; $cast: ty) => {
        $(
            impl TryFrom<IntConstant> for $ty {
                type Error = ();

                fn try_from(value: IntConstant) -> Result<Self, Self::Error> {
                    debug_assert!(value.is_small());
                    <$cast>::from_be_bytes(value.get_bytes()).try_into().map_err(|_| ())
                }
            }
        )*
    };
    () => {
    };
}

int_const_impl_into!(i8, i16, i32, i64, isize, i128; i128);
int_const_impl_into!(u8, u16, u32, u64, usize, u128; u128);

counter! {
    name: InternedInt,
    counter_name: INTERNED_INT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl fmt::Display for IntConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            // We want to snip the value from the `total` value since we don't care about the
            // rest...
            IntConstantValue::Small(value) => {
                if self.is_signed() {
                    write!(f, "{}", i128::from_be_bytes(*value))?;
                } else {
                    write!(f, "{}", u128::from_be_bytes(*value))?;
                }
            }
            IntConstantValue::Big(value) => write!(f, "{value}")?,
        }

        write!(f, "_{}", self.ty)
    }
}

impl fmt::Display for InternedInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_int_constant(*self))
    }
}

counter! {
    name: InternedStr,
    counter_name: STR_LIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        let constant =
            FloatConstant { value: FloatConstantValue::F64(value), ty: FloatTy::F64, suffix };
        self.create_float_constant(constant)
    }

    /// Create a `f32` [FloatConstant] within the [ConstantMap]
    pub fn create_f32_float_constant(
        &self,
        value: f32,
        suffix: Option<Identifier>,
    ) -> InternedFloat {
        let constant =
            FloatConstant { value: FloatConstantValue::F32(value), ty: FloatTy::F32, suffix };
        self.create_float_constant(constant)
    }

    /// Create a [FloatConstant] within the [ConstantMap]
    pub fn create_float_constant(&self, constant: FloatConstant) -> InternedFloat {
        let ident = InternedFloat::new();
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
    pub fn create_int_constant(&self, constant: IntConstant) -> InternedInt {
        let ident = InternedInt::new();

        // Insert the entries into the map and the reverse-lookup map
        self.int_table.insert(ident, constant);
        ident
    }

    /// Get the [IntConstant] behind the [InternedInt]
    pub fn lookup_int_constant(&self, id: InternedInt) -> IntConstant {
        let lookup_value = self.int_table.get(&id).unwrap();
        let IntConstant { value, ty, suffix } = lookup_value.value();

        let value = match value {
            IntConstantValue::Small(inner) => IntConstantValue::Small(*inner),
            IntConstantValue::Big(inner) => IntConstantValue::Big(inner.clone()),
        };

        IntConstant { value, ty: *ty, suffix: *suffix }
    }

    /// Perform a transformation on the [IntConstant] behind the [InternedInt]
    /// without making a copy of the original value.
    pub fn map_int_constant<T>(&self, id: InternedInt, f: impl FnOnce(&IntConstant) -> T) -> T {
        let lookup_value = self.int_table.get(&id).unwrap();
        f(lookup_value.value())
    }

    /// Perform a transformation on the [FloatConstant] behind the
    /// [InternedFloat] without making a copy of the original value.
    pub fn map_float_constant<T>(
        &self,
        id: InternedFloat,
        f: impl FnOnce(&FloatConstant) -> T,
    ) -> T {
        let lookup_value = self.float_table.get(&id).unwrap();
        f(lookup_value.value())
    }

    /// Perform a negation operation on an [InternedInt].
    ///
    /// N.B: This function has no effect on the stored constant if it is not
    /// signed.
    pub fn negate_int_constant(&self, id: InternedInt) {
        self.int_table.alter(&id, |_, value| value.negate());
    }
}

#[cfg(test)]
mod tests {
    use hash_target::{
        primitives::{SIntTy, UIntTy},
        size::Size,
    };
    use num_bigint::BigInt;

    use crate::constant::IntConstantValue;

    #[test]
    fn test_max_signed_int_value() {
        // Pointer width is always described using a number of bytes
        assert_eq!(SIntTy::ISize.max(8), Some(BigInt::from(isize::MAX)));
        assert_eq!(SIntTy::ISize.min(8), Some(BigInt::from(isize::MIN)));

        assert_eq!(SIntTy::ISize.max(4), Some(BigInt::from(i32::MAX)));
        assert_eq!(SIntTy::ISize.min(4), Some(BigInt::from(i32::MIN)));

        // Check that computing the size of each type with pointer widths
        // is consistent.
        assert_eq!(SIntTy::ISize.size(8), Some(Size::from_bytes(8)));
        assert_eq!(SIntTy::ISize.size(4), Some(Size::from_bytes(4)));
    }

    #[test]
    fn test_max_unsigned_int_value() {
        // We don't check `min()` for unsigned since this always
        // returns 0.
        assert_eq!(UIntTy::USize.max(8), Some(BigInt::from(usize::MAX)));
        assert_eq!(UIntTy::USize.max(4), Some(BigInt::from(u32::MAX)));

        assert_eq!(UIntTy::USize.size(4), Some(Size::from_bytes(4)));
        assert_eq!(UIntTy::USize.size(8), Some(Size::from_bytes(8)));
    }

    #[test]
    fn test_int_constant_conversions() {
        let value = -7i32;
        let constant = IntConstantValue::from_le_bytes(&value.to_le_bytes());
        assert_eq!(
            IntConstantValue::Small([
                255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 249
            ]),
            constant
        );

        let value = -7i32;
        let constant = IntConstantValue::from_le_bytes(&value.to_le_bytes());
        assert_eq!(
            IntConstantValue::Small([
                255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 249
            ]),
            constant
        );

        let value = 7i32;
        let constant = IntConstantValue::from_le_bytes(&value.to_le_bytes());
        assert_eq!(
            IntConstantValue::Small([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7]),
            constant
        );
    }
}
