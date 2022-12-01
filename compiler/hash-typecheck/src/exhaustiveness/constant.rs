//! Utilities for converting literal terms that are used within the typechecker
//! to represent literals, and convert them into a `ConstantValue` which is
//! used within the exhaustiveness sub-system to represent these values within
//! a single data type.
use hash_source::constant::{InternedInt, CONSTANT_MAP};
use hash_types::terms::TermId;

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

    /// Function to convert a [InternedInt] into a [Constant]. The only
    /// constraint is that it can fit into a [u128], otherwise the
    /// function will currently panic.
    pub fn from_int(value: InternedInt, ty: TermId, ptr_width: usize) -> Self {
        let kind = CONSTANT_MAP.map_int_constant(value, |value| value.ty);
        let bytes = kind.size(ptr_width).unwrap().bytes() as usize;

        // Get the associated bytes with the interned-int so we can convert
        // into a constant.
        let mut data = CONSTANT_MAP.lookup_int_constant(value).get_bytes();

        // memset the upper 16-kind.size() bytes to zero since they aren't
        // necessary.
        if kind.is_signed() {
            data[0..(16 - bytes)].fill(0);
        }

        Constant { data: u128::from_be_bytes(data), ty }
    }

    /// Get the data stored within the [Constant].
    pub fn data(&self) -> u128 {
        self.data
    }
}
