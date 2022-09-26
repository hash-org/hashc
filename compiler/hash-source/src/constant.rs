//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{fmt::Display, ops::Neg};

use dashmap::DashMap;
use fnv::FnvBuildHasher;
use hash_utils::counter;
use lazy_static::lazy_static;
use num_bigint::BigInt;

use crate::identifier::{Identifier, CORE_IDENTIFIERS};

/// Interned float constant which stores the value of the float, and
/// an optional `type ascription` which is a suffix on the literal
/// describing which float kind it is, either being `f32` or `f64`.
#[derive(Debug, Clone, Copy)]
pub struct FloatConstant {
    /// Raw value of the float
    pub value: [u8; 8],
    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32.4f64`
    pub suffix: Option<Identifier>,
}

impl FloatConstant {
    /// Perform a negation operation on the [FloatConstant].
    pub fn negate(self) -> Self {
        // @@Todo: handle the case when the variable is typed as a `f32`
        let value = -f64::from_be_bytes(self.value);

        Self { value: value.to_be_bytes(), suffix: self.suffix }
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
        if let Some(suffix) = self.suffix && suffix == CORE_IDENTIFIERS.f64 {
            write!(f, "{}", f64::from_be_bytes(self.value))?;    
        } else {
            let value = self.value[4..].try_into().unwrap();
            write!(f, "{}", f32::from_be_bytes(value))?;    
        }

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
                i if CORE_IDENTIFIERS.i8 == i => true,
                i if CORE_IDENTIFIERS.i16 == i => true,
                i if CORE_IDENTIFIERS.i32 == i => true,
                i if CORE_IDENTIFIERS.i64 == i => true,
                i if CORE_IDENTIFIERS.i128 == i => true,
                i if CORE_IDENTIFIERS.isize == i => true,
                i if CORE_IDENTIFIERS.ibig == i => true,
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
            IntConstantValue::Big(value) => write!(f, "{}", value)?,
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

    /// Create a [FloatConstant] within the [ConstantMap]
    pub fn create_float_constant(&self, value: f64, suffix: Option<Identifier>) -> InternedFloat {
        let ident = InternedFloat::new();
        let constant = FloatConstant { value: value.to_be_bytes(), suffix };

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
