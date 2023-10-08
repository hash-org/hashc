//! Utilities and logic for dealing with ADT discriminants. This module defines
//! a core [Discriminant] type which allows the user to represent and operate on
//! discriminant values.

use crate::{primitives::IntTy, size::Size, HasTarget};

/// A utility for working with constructor discriminants.
#[derive(Debug, Clone, Copy)]
pub struct Discriminant {
    /// The actual value of the discriminant.
    pub value: u128,

    /// The annotated type of the discriminant.
    pub ty: IntTy,

    /// The kind of discriminant, whether it is an explicitly specified one, or
    /// if it is relative to the previous discriminant.
    pub kind: DiscriminantKind,
}

impl Discriminant {
    /// Create an initial value for a [Discriminant].
    pub fn initial(ty: IntTy) -> Self {
        Self { value: 0, ty, kind: DiscriminantKind::Relative(0) }
    }

    /// Check whether the value of the current [Discriminant] has overflowed
    /// beyond the specified discriminant type.
    ///
    /// ##Hack: This function is stupid because it always assumes that the discriminant
    /// value from expansion is parsed as a full i128, and hence we can actually
    /// do the comparison of the signed min/max values.
    pub fn has_overflowed<E: HasTarget>(&self, env: &E) -> bool {
        let size = self.ty.size(env.target().ptr_size());

        if self.ty.is_signed() {
            let val = self.value as i128;
            let min = size.signed_int_min();
            let max = size.signed_int_max();
            val < min || val > max
        } else {
            let max = size.unsigned_int_max();
            self.value > max
        }
    }

    /// Implements checked addition onto the discriminant, accounting
    /// for signedness of the discriminant and overflow.
    pub fn checked_add<E: HasTarget>(self, env: &E, n: u128) -> (Self, bool) {
        let size = self.ty.size(env.target().ptr_size());

        let (value, overflow) = if self.ty.is_signed() {
            let min = size.signed_int_min();
            let max = size.signed_int_max();
            let val = size.sign_extend(self.value) as i128;
            debug_assert!(n < (i128::MAX as u128));

            let n = n as i128;
            let overflow = val > max - n;
            let val = if overflow { min + (n - (max - val) - 1) } else { val + n };
            let val = size.truncate(val as u128);
            (val, overflow)
        } else {
            let max = size.unsigned_int_max();
            let val = self.value;
            let overflow = val > max - n;
            let val = if overflow { n - (max - val) - 1 } else { val + n };
            (val, overflow)
        };

        let kind = match self.kind {
            DiscriminantKind::Relative(0) => DiscriminantKind::implicit(),
            DiscriminantKind::Relative(n) => DiscriminantKind::Relative(n + 1),
            DiscriminantKind::Explicit => DiscriminantKind::Relative(1),
        };

        (Self { value, ty: self.ty, kind }, overflow)
    }

    /// Convert the [Discriminant] into a [String] representation,
    ///
    /// the pointer size is required to perform the conversion (for
    /// usize/isizes).
    ///
    /// @@Todo: re-work Target/TargetDataLayout relationship.
    pub fn to_string(&self, ptr_size: Size) -> String {
        // let size = self.ty.size(env.target().ptr_size());
        let size = self.ty.size(ptr_size);

        if self.ty.is_signed() {
            let val = size.sign_extend(self.value) as i128;
            format!("{}", val)
        } else {
            format!("{}", self.value)
        }
    }
}

/// Denotes the way that the discriminant was computed/specified.
#[derive(Debug, Clone, Copy)]
pub enum DiscriminantKind {
    /// If the relative index is set to `0`, then this means that the
    /// discriminant has no previous discriminant to be relative to.
    Relative(u32),

    /// The discriminant was explicitly stated.
    Explicit,
}

impl DiscriminantKind {
    /// Create an implicit [DiscriminantKind].
    #[inline(always)]
    pub fn implicit() -> Self {
        Self::Relative(0)
    }
}
