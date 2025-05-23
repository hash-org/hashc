//! Trait methods to do with emitting types for the backend.

use hash_abi::FnAbi;
use hash_ir::ty::{ReprTy, ReprTyId};
use hash_repr::TyInfo;
use hash_source::constant::FloatTy;
use hash_storage::store::statics::StoreId;
use hash_target::abi::{AddressSpace, Integer};

use super::{BackendTypes, layout::LayoutMethods};
use crate::common::TypeKind;

pub trait TypeBuilderMethods<'b>: BackendTypes + LayoutMethods<'b> {
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

    /// Create a integer type of an arbitrary size, i.e. `i19`, `u126`, etc.
    fn type_ix(&self, bits: u64) -> Self::Type;

    /// Create a C `int` type, this will depend on the
    /// compilation target.
    fn type_int(&self) -> Self::Type {
        match &self.target().c_int_width {
            16 => self.type_i16(),
            32 => self.type_i32(),
            64 => self.type_i64(),
            _ => unreachable!("unsupported integer width"),
        }
    }

    /// Create a integer type from the specified [abi::Integer].
    fn type_from_integer(&self, int: Integer) -> Self::Type {
        match int {
            Integer::I8 => self.type_i8(),
            Integer::I16 => self.type_i16(),
            Integer::I32 => self.type_i32(),
            Integer::I64 => self.type_i64(),
            Integer::I128 => self.type_i128(),
        }
    }

    /// Create a float type.
    fn type_f32(&self) -> Self::Type;

    /// Create a double type.
    fn type_f64(&self) -> Self::Type;

    /// Create a float type from the specified [FloatTy].
    fn type_from_float(&self, ty: FloatTy) -> Self::Type {
        match ty {
            FloatTy::F32 => self.type_f32(),
            FloatTy::F64 => self.type_f64(),
        }
    }

    /// Create an array type.
    fn type_array(&self, ty: Self::Type, len: u64) -> Self::Type;

    /// Create a function type.
    fn type_function(&self, args: &[Self::Type], ret: Self::Type) -> Self::Type;

    /// Create a struct type.
    fn type_struct(&self, els: &[Self::Type], packed: bool) -> Self::Type;

    /// Create an opaque pointer type.
    fn type_ptr(&self) -> Self::Type;

    /// Create an opaque pointer type with a specified [AddressSpace].
    fn type_ptr_ext(&self, address_space: AddressSpace) -> Self::Type;

    /// Get the element type of a given type.
    fn element_type(&self, ty: Self::Type) -> Self::Type;

    /// Returns the number of elements in `self` if it is a LLVM vector type.
    fn vector_length(&self, ty: Self::Type) -> usize;

    /// Returns the width of the float type `self`.
    fn float_width(&self, ty: Self::Type) -> usize;

    /// Retrieves the bit width of the integer type `self`.
    fn int_width(&self, ty: Self::Type) -> u64;

    /// Compute the type of a particular backend value.
    fn ty_of_value(&self, value: Self::Value) -> Self::Type;

    /// Get the [TypeKind] of a particular type.
    fn ty_kind(&self, ty: Self::Type) -> TypeKind;

    /// Create a new "immediate" backend type. This is mainly
    /// used for constants and ZSTs.
    fn immediate_backend_ty(&self, info: TyInfo) -> Self::Type;

    /// Get the type of an element from a scalar pair, and assume
    /// if it "immediate".
    fn scalar_pair_element_backend_ty(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type;

    /// Create a backend specific type from a [TyInfo].
    fn backend_ty_from_info(&self, info: TyInfo) -> Self::Type;

    /// Create a backend type that represents the provided [FnAbi]. This
    /// is used to compute a function type from a [FnAbi].
    fn backend_ty_from_abi(&self, abi: &FnAbi) -> Self::Type;

    /// Check whether a given type has additional hidden metadata like the
    /// size of a slice or a string.
    fn ty_has_hidden_metadata(&self, ty: ReprTyId) -> bool {
        ty.map(|ty| matches!(ty, ReprTy::Slice(_) | ReprTy::Str))
    }
}
