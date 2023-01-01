//! Trait methods to do with emitting types for the backend.

use hash_target::abi::AddressSpace;

use super::Backend;
use crate::common::TypeKind;

pub trait BuildTypeMethods<'b>: Backend<'b> {
    /// Create a bit type.
    fn type_i1(&self) -> Self::Type;

    /// Create an 8-bit integer type.
    fn type_i8(&self) -> Self::Type;

    /// Create a 16-bit integer type.
    fn type_i16(&self) -> Self::Type;

    /// Create a 32-bit integer type.
    fn type_i32(&self) -> Self::Type;

    /// Create a 64-bit integer type.
    fn type_i64(&self) -> Self::Type;

    /// Create a 128-bit integer type.
    fn type_i128(&self) -> Self::Type;

    /// Create a `isize` type.
    fn type_isize(&self) -> Self::Type;

    /// Create a float type.
    fn type_f32(&self) -> Self::Type;

    /// Create a double type.
    fn type_f64(&self) -> Self::Type;

    /// Create an array type.
    fn type_array(&self, ty: Self::Type, len: u64) -> Self::Type;

    /// Create a function type.
    fn type_function(&self, args: &[Self::Type], ret: Self::Type) -> Self::Type;

    /// Create a struct type.
    fn type_struct(&self, els: &[Self::Type], packed: bool) -> Self::Type;

    /// Get the [TypeKind] of a particular type.
    fn type_kind(&self, ty: Self::Type) -> TypeKind;

    /// Create a pointer type to `ty`.
    fn type_ptr_to(&self, ty: Self::Type) -> Self::Type;

    /// Create a pointer type to `ty` with the given address space.
    fn type_ptr_to_ext(&self, ty: Self::Type, address_space: AddressSpace) -> Self::Type;

    fn element_type(&self, ty: Self::Type) -> Self::Type;

    /// Returns the number of elements in `self` if it is a LLVM vector type.
    fn vector_length(&self, ty: Self::Type) -> usize;

    /// Returns the width of the float type `self`.
    fn float_width(&self, ty: Self::Type) -> usize;

    /// Retrieves the bit width of the integer type `self`.
    fn int_width(&self, ty: Self::Type) -> u64;
}
