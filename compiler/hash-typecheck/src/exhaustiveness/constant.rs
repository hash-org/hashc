//! Utilities for converting literal terms that are used within the typechecker
//! to represent literals, and convert them into a `ConstantValue` which is
//! used within the exhaustiveness sub-system to represent these values within
//! a single data type.
use hash_source::constant::IntTy;
use hash_types::terms::TermId;
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
    pub fn from_int(int: BigInt, kind: IntTy, ty: TermId, ptr_width: usize) -> Self {
        let size = kind.size(ptr_width).unwrap_or_else(|| int.bits());
        assert!(size < 128);

        // @@Hack: this should be done in some better way or tidied up!
        // This is here because `BigInt::to_be_bytes()` returns the minimum
        // number of bytes rather than providing functions that could coerce the
        // type into another. Since we work with only `u128` we need to
        // perform this ugly bit shifts in order for this to work...
        if kind.is_signed() {
            // Cast the `bigint` into a i128 and then convert to big-endian bytes
            let mut data = (<BigInt as TryInto<i128>>::try_into(int).unwrap()).to_be_bytes();

            // memset the upper 16-kind.size() bytes to zero since they aren't
            // necessary.
            data[0..(16 - kind.size(ptr_width).unwrap() as usize)].fill(0);

            Constant { data: u128::from_be_bytes(data), ty }
        } else {
            let (_, data) = int.into_parts();
            Constant { data: data.try_into().unwrap(), ty }
        }
    }

    /// Get the data stored within the [Constant].
    pub fn data(&self) -> u128 {
        self.data
    }
}
