//! Utilities for converting literal terms that are used within the typechecker
//! to represent literals, and convert them into a `ConstantValue` which is
//! used within the exhaustiveness sub-system to represent these values within
//! a single data type.
//!
//! **Note**:
//!
//! The defined API is only temporary and is an initial attempt to create
//! an ABI for Hash, it is subject to change and is incomplete.

use crate::storage::primitives::{IntKind, TermId};
use num_bigint::BigInt;

#[derive(Debug, Clone, Copy)]
pub struct Constant {
    /// The scalar data that is stored from the constant
    data: u128,
    /// The type of the constant. This should always be a primitive type
    /// that the size of the type can be computed.
    pub ty: TermId,
}

impl Constant {
    /// Convert a character into a constant.
    pub fn from_char(c: char, ty: TermId) -> Self {
        Constant { data: c.into(), ty }
    }

    /// Convert a 128bit integer into a constant.
    pub fn from_u128(num: u128, ty: TermId) -> Self {
        Constant { data: num, ty }
    }

    /// Function to convert a [BigInt] into a [Constant]. The only
    /// constraint is that it can fit into a [u128], otherwise the
    /// function will currently panic.
    pub fn from_int(int: BigInt, kind: IntKind, ty: TermId) -> Self {
        let size = kind.size().unwrap_or_else(|| int.bits());
        assert!(size < 128);

        let (.., data) = int.into_parts();
        Constant { data: data.try_into().unwrap(), ty }
    }

    /// Get the data stored within the [Constant].
    pub fn data(&self) -> u128 {
        self.data
    }
}
