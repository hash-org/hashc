//! This module defines all the core data structures that deal with
//! the alignment of data types within Hash and the compiler. This
//! is primarily used after the lowering stage to represent and deal
//! with alignment.

use std::fmt;

use crate::size::Size;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AlignmentError {
    /// The provided alignment size is not a power of two.
    NotPowerOfTwo,

    /// The provided alignment value is too large.
    TooLarge,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Alignment {
    /// The alignment of the data in powers of two bytes.
    ///
    /// N.B. The alignment is always a power of two, and is always
    /// between the range of `1` and `32` since LLVM does not
    /// support alignments greater than `2^32`.
    ///
    /// Ref: https://llvm.org/docs/LangRef.html#id203
    value: u8,
}

impl fmt::Display for Alignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // get the nice bytes unit for the alignment
        let size = Size::from_bytes(self.bytes());
        write!(f, "{size}")
    }
}

impl fmt::Debug for Alignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "align[value={}]", self.bytes())
    }
}

impl Alignment {
    pub const ONE: Alignment = Alignment { value: 0 };
    pub const MAX: Alignment = Alignment { value: 32 };

    /// Create a new alignment from the given alignment in bits. If
    /// the specified alignment value is invalid, then an [AlignmentError]
    /// is returned.
    #[inline]
    pub fn from_bits(size: u64) -> Result<Alignment, AlignmentError> {
        Alignment::from_bytes(Size::from_bits(size).bytes())
    }

    /// Create a new alignment from the given alignment in bytes. If
    /// the specified alignment value is invalid, then an [AlignmentError]
    /// is returned.
    #[inline]
    pub fn from_bytes(size: u64) -> Result<Alignment, AlignmentError> {
        // First check if the size is zero, and if so then we return
        // the minimum alignment of 1.
        if size == 0 {
            return Ok(Alignment::ONE);
        }

        let mut bytes = size;
        let mut value: u8 = 0;

        while (bytes & 1) == 0 {
            bytes >>= 1;
            value += 1;
        }

        // If we reached a non-one value, then the value was not
        // a power of two.
        if bytes != 1 {
            return Err(AlignmentError::NotPowerOfTwo);
        }

        // Check if the alignment is too large.
        if value > Self::MAX.value {
            return Err(AlignmentError::TooLarge);
        }

        Ok(Alignment { value })
    }

    /// Get the alignment value in bytes.
    #[inline]
    pub fn bytes(&self) -> u64 {
        1 << self.value
    }

    /// Get the alignment value in bits.
    #[inline]
    pub fn bits(&self) -> u64 {
        self.bytes() * 8
    }

    /// Lower the [Alignment], if necessary, such that the given `offset`
    /// is aligned to it (the offset is a multiple of the alignment).
    ///
    /// The size of the offset is computed by finding the minimum alignment
    /// needed for `offset`, i.e. the largest power of two that the offset is a
    /// multiple of.
    ///
    /// N.B. A [Size] of zero is always aligned to any alignment.
    #[inline]
    pub fn restrict_to(self, offset: Size) -> Alignment {
        let size = Alignment { value: offset.bytes().trailing_zeros() as u8 };

        self.min(size)
    }
}

/// A pair of [Alignment]s which represent the ABI specified
/// [Alignment] and a "preferred" [Alignment].
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Alignments {
    /// The ABI specified alignment.
    pub abi: Alignment,

    /// The preferred alignment.
    pub preferred: Alignment,
}

impl Alignments {
    /// Create a new [Alignments] pair.
    pub fn new(align: Alignment) -> Alignments {
        Alignments { abi: align, preferred: align }
    }

    /// Get the minimum of two [Alignments].
    #[inline]
    pub fn min(self, other: Alignments) -> Alignments {
        Alignments { abi: self.abi.min(other.abi), preferred: self.preferred.min(other.preferred) }
    }

    /// Get the maximum of two [Alignments].
    #[inline]
    pub fn max(self, other: Alignments) -> Alignments {
        Alignments { abi: self.abi.max(other.abi), preferred: self.preferred.max(other.preferred) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bad_alignments() {
        // The creation of all of these alignments should fail
        // since they are not powers of two or too large.
        assert!(Alignment::from_bytes(3).is_err());
        assert!(Alignment::from_bytes(2 << 33).is_err());

        // 64 bits is too large.
        assert!(Alignment::from_bits(2 << 47).is_err());
    }

    #[test]
    fn test_valid_alignments() {
        // special case, `0` size is aligned to `1`.
        assert_eq!(Alignment::from_bytes(0), Ok(Alignment::ONE));

        // The creation of all of these alignments should succeed.
        assert!(Alignment::from_bytes(1).is_ok());
        assert!(Alignment::from_bytes(2).is_ok());
        assert!(Alignment::from_bytes(4).is_ok());
        assert!(Alignment::from_bytes(8).is_ok());
        assert!(Alignment::from_bytes(16).is_ok());
        assert!(Alignment::from_bytes(32).is_ok());

        assert_eq!(Alignment::from_bits(32), Ok(Alignment { value: 2 }));
    }

    #[test]
    fn test_alignment_restrictions() {
        let align = Alignment::from_bytes(8).unwrap();

        // restrict alignment to various sizes
        assert_eq!(align.restrict_to(Size::from_bytes(4)), Alignment::from_bytes(4).unwrap());
        assert_eq!(align.restrict_to(Size::from_bytes(6)), Alignment::from_bytes(2).unwrap());
        assert_eq!(align.restrict_to(Size::from_bytes(8)), Alignment::from_bytes(8).unwrap());

        // O bytes does not affect the alignment.
        assert_eq!(align.restrict_to(Size::from_bytes(0)), Alignment::from_bytes(8).unwrap());
    }
}
