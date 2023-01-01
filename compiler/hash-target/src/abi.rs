//! This module defines types and logic that deal with ABIs (Application Binary
//! Interfaces). This is needed in order to communicate with the outside world
//! and to be able to call functions from other languages, but to also provide
//! information to code generation backends about how values are represented.

use crate::{alignment::Alignments, layout::HasDataLayout, size::Size};

/// ABI representation of an integer scalar type.
#[derive(Clone, Copy, Debug)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl Integer {
    /// Compute the [Size] of the [Integer].
    #[inline]
    pub fn size(self) -> Size {
        use Integer::*;

        match self {
            I8 => Size::from_bytes(1),
            I16 => Size::from_bytes(2),
            I32 => Size::from_bytes(4),
            I64 => Size::from_bytes(8),
            I128 => Size::from_bytes(16),
        }
    }

    /// Get the [Alignments] of the [Integer].
    pub fn align<C: HasDataLayout>(self, ctx: &C) -> Alignments {
        use Integer::*;
        let dl = ctx.data_layout();

        match self {
            I8 => dl.i8_align,
            I16 => dl.i16_align,
            I32 => dl.i32_align,
            I64 => dl.i64_align,
            I128 => dl.i128_align,
        }
    }
}

/// ABI representation of a float scalar type.
#[derive(Clone, Copy, Debug)]
pub enum Float {
    /// A 32-bit float.
    F32,

    /// A 64-bit float.
    F64,
}

impl Float {
    /// Compute the [Size] of the [Float].
    #[inline]
    pub fn size(self) -> Size {
        use Float::*;
        match self {
            F32 => Size::from_bytes(2),
            F64 => Size::from_bytes(4),
        }
    }

    /// Get the [Alignments] of the [Float].
    pub fn align<C: HasDataLayout>(self, cx: &C) -> Alignments {
        use Float::*;
        let dl = cx.data_layout();

        match self {
            F32 => dl.f32_align,
            F64 => dl.f64_align,
        }
    }
}

/// Represents all of the primitive [AbiRepresentation::Scalar]s that are
/// supported within the ABI.
#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    /// An integer scalar.
    Int { kind: Integer, signed: bool },

    /// A float scalar.
    Float { kind: Float },

    /// A pointer primitive scalar value.
    Pointer,
}

impl Primitive {
    /// Align the [Primitive] with the current data layout
    /// specification.
    pub fn align<L: HasDataLayout>(&self, ctx: &L) -> Alignments {
        let dl = ctx.data_layout();

        match self {
            Primitive::Int { kind, .. } => kind.align(ctx),
            Primitive::Float { kind } => kind.align(ctx),
            Primitive::Pointer => dl.pointer_align,
        }
    }

    /// Compute the size of the [Primitive].
    pub fn size<L: HasDataLayout>(&self, ctx: &L) -> Size {
        let dl = ctx.data_layout();

        match self {
            Primitive::Int { kind, .. } => kind.size(),
            Primitive::Float { kind } => kind.size(),
            Primitive::Pointer => dl.pointer_size,
        }
    }
}

/// This defined how values are being represented and are passed by target
/// ABIs in the terms of c-type categories.
#[derive(Debug)]
pub enum AbiRepresentation {
    /// A value that is not represented in memory, but is instead passed
    /// by value. This is used for values that are smaller than a pointer
    Uninhabited,

    /// A scalar value.
    Scalar { kind: Primitive },

    /// A vector value.
    Vector {
        /// The number of elements in the vector.
        elements: u64,

        /// The kind of the vector.
        kind: Primitive,
    },

    /// An aggregate value.
    Aggregate,
}

/// An identifier that specifies the address space that some operation
/// should operate on. Special address spaces have an effect on code generation,
/// depending on the target and the address spaces it implements.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AddressSpace(pub u32);

impl AddressSpace {
    /// The default address space, corresponding to data space.
    pub const DATA: Self = AddressSpace(0);
}
