//! Utilities for converting literal terms that are used within the typechecker
//! to represent literals, and convert them into a `ConstantValue` which is
//! used within the exhaustiveness sub-system to represent these values within
//! a single data type.
use hash_source::constant::InternedInt;
use hash_tir::nodes::terms::TyId;

#[derive(Debug, Clone, Copy)]
pub struct Constant {
    /// The scalar data that is stored from the constant
    data: u128,
    /// The type of the constant. This should always be a primitive type
    /// that the size of the type can be computed.
    pub ty: TyId,
}

impl Constant {
    /// Convert a character into a constant.
    pub fn from_char(c: char, ty: TyId) -> Self {
        Constant { data: c.into(), ty }
    }

    /// Convert a 128bit integer into a constant.
    pub fn from_u128(num: u128, ty: TyId) -> Self {
        Constant { data: num, ty }
    }

    /// Function to convert a [InternedInt] into a [Constant]. The only
    /// constraint is that it can fit into a [u128], otherwise the
    /// function will currently panic.
    pub fn from_int(constant: InternedInt, ty: TyId) -> Self {
        // Get the associated bytes with the interned-int so we can convert
        // into a constant.
        let data = constant.value().value.as_u128();
        Constant { data, ty }
    }

    /// Get the data stored within the [Constant].
    pub fn data(&self) -> u128 {
        self.data
    }
}
