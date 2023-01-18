//! Represents all of the logic related to type sizes, and various
//! utilities surrounding type sizes.

use std::{
    fmt,
    ops::{Add, Mul, Sub},
};

use crate::{alignment::Alignment, data_layout::HasDataLayout};

/// Represents the size of some constant in bytes. [Size] is a
/// utility type that allows one to perform various conversions
/// on the size (bits and bytes), and to derive .
#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    value: u64,
}

impl fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (value, unit) = self.into_units();
        write!(f, "{value}{unit}")
    }
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

    /// Compute a human readable unit for the [Size].
    pub fn into_units(self) -> (usize, &'static str) {
        let bytes = self.bytes();

        if bytes >= 1 << 30 {
            (bytes as usize / (1 << 30), "Gb")
        } else if bytes >= 1 << 20 {
            (bytes as usize / (1 << 20), "Mb")
        } else if bytes >= 1 << 10 {
            (bytes as usize / (1 << 10), "Kb")
        } else {
            (bytes as usize, "b")
        }
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

    /// Get the maximum unsigned integer value that is
    /// representable within this size.
    #[inline]
    pub fn unsigned_int_max(&self) -> u128 {
        u128::MAX >> (128 - self.bits())
    }

    /// Take the current [Size] and align it to a specified [Alignment].
    ///
    /// N.B. Passing [`Size::ZERO`] will result in no change.
    pub fn align_to(&self, alignment: Alignment) -> Size {
        // Create a mask for the alignment, add it to the
        // current size to account for the alignment, and then
        // trim the size to remove any slack.
        let mask = alignment.bytes() - 1;
        Size::from_bytes((self.bytes() + mask) & !mask)
    }

    /// Compute a checked multiplication operation with a provided
    /// [HasDataLayout] context. If the total size exceeds the
    /// maximum size of the largest target object size, then
    /// this value cannot be represented for the current target
    /// and thus the function will return [`None`].
    pub fn checked_mul<C: HasDataLayout>(self, count: u64, ctx: &C) -> Option<Size> {
        let dl = ctx.data_layout();
        let bytes = self.bytes().checked_mul(count)?;

        if bytes < dl.obj_size_bound() {
            Some(Size::from_bytes(bytes))
        } else {
            None
        }
    }

    /// Compute a checked addition operation with a provided
    /// [HasDataLayout] context. If the total size exceeds the
    /// maximum size of the largest target object size, then
    /// this value cannot be represented for the current target
    /// and thus the function will return [`None`].
    pub fn checked_add<C: HasDataLayout>(self, value: Size, ctx: &C) -> Option<Size> {
        let dl = ctx.data_layout();
        let bytes = self.bytes().checked_add(value.bytes())?;

        if bytes < dl.obj_size_bound() {
            Some(Size::from_bytes(bytes))
        } else {
            None
        }
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

impl Sub for Size {
    type Output = Size;
    #[inline]
    fn sub(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_sub(other.bytes()).unwrap_or_else(|| {
            panic!("Size::sub: {} - {} would result in negative size", self.bytes(), other.bytes())
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
