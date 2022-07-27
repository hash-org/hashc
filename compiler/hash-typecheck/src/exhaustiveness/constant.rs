//! Utilities for converting literal terms that are used within the typechecker
//! to represent literals, and convert them into a `ConstantValue` which is
//! used within the exhaustiveness sub-system to represent these values within
//! a single data type.
//!
//! **Note**:
//!
//! The defined API is only temporary and is an initial attempt to create
//! an ABI for Hash, it is subject to change and is incomplete.

use crate::storage::primitives::TermId;
use num_bigint::BigInt;
use std::num::NonZeroU8;

pub struct Constant {
    /// The scalar data that is stored from the constant
    data: u128,
    /// The size of the data in bits.
    size: NonZeroU8,
    /// The type of the constant. This should always be a primitive type
    /// that the size of the type can be computed.
    ty: TermId,
}

impl Constant {
    /// Convert a character into a constant.
    pub fn from_char(c: char, ty: TermId) -> Self {
        let char_size = std::mem::size_of::<char>();
        let size = NonZeroU8::new(char_size.try_into().unwrap()).unwrap();

        Constant { data: c.into(), size, ty }
    }

    /// Function to convert a [BigInt] into a [Constant]. The only
    /// constraint is that it can fit into a [u128], otherwise the
    /// function will currently panic.
    pub fn from_int(int: BigInt, ty: TermId) -> Self {
        let size = int.bits();
        assert!(size < 128);

        let (.., data) = int.into_parts();
        Constant {
            data: data.try_into().unwrap(),
            size: NonZeroU8::new(size.try_into().unwrap()).unwrap(),
            ty,
        }
    }
}
