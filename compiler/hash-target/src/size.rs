//! Represents all of the logic related to type sizes, and various
//! utilities surrounding type sizes.

use std::ops::{Add, Mul};

/// Represents the size of some constant in bytes. [Size] is a
/// utility type that allows one to perform various conversions
/// on the size (bits and bytes), and to derive .
#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    value: u64,
}

impl Size {
    /// The [Size::ZERO] is often used for type of size 0.
    pub const ZERO: Size = Size { value: 0 };

    /// Create a [Size] from the number of bytes.
    pub fn from_bytes(value: impl TryInto<u64>) -> Self {
        Self { value: value.try_into().ok().unwrap() }
    }

    /// Create a [Size] from the number of bits. This function will
    /// rounds `value` up to the next-higher byte boundary, if `bits` is
    /// not a multiple of 8.
    pub fn from_bits(value: impl TryInto<u64>) -> Self {
        let bits = value.try_into().ok().unwrap();

        // Avoid potential overflow from `bits + 7`.
        Size { value: bits / 8 + ((bits % 8) + 7) / 8 }
    }

    /// Return the [Size] in bytes.
    #[inline]
    pub fn bytes(self) -> u64 {
        self.value
    }

    /// Convert the [Size] into the number of bits.
    #[inline]
    pub fn bits(self) -> u64 {
        self.value * 8
    }

    /// Truncates `value` to `self` bits.
    #[inline]
    pub fn truncate(self, value: u128) -> u128 {
        let size = self.bits();
        if size == 0 {
            // Truncated until nothing is left.
            return 0;
        }

        let shift = 128 - size;
        // Truncate (shift left to drop out leftover values, shift right to fill with
        // zeroes).
        (value << shift) >> shift
    }
}

impl Add for Size {
    type Output = Size;
    #[inline]
    fn add(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_add(other.bytes()).unwrap_or_else(|| {
            panic!("Size::add: {} + {} doesn't fit in u64", self.bytes(), other.bytes())
        }))
    }
}

impl Mul<Size> for u64 {
    type Output = Size;
    #[inline]
    fn mul(self, size: Size) -> Size {
        size * self
    }
}

impl Mul<u64> for Size {
    type Output = Size;
    #[inline]
    fn mul(self, count: u64) -> Size {
        match self.bytes().checked_mul(count) {
            Some(bytes) => Size::from_bytes(bytes),
            None => panic!("Size::mul: {} * {} doesn't fit in u64", self.bytes(), count),
        }
    }
}
