//! This file defines a trait [`BuildConstValueMethods`] that enables the
//! backend builder to emit constants of all primitive types when converting
//! Hash IR into the target backend.

use super::BackendTypes;

/// Trait that represents methods for emitting constants
/// when building the IR.
pub trait BuildConstValueMethods<'b>: BackendTypes {
    /// Emit a constant undefined value, this is use for generating
    /// zero-sized types.
    fn const_undef(&self, ty: Self::Type) -> Self::Value;

    /// Emit a constant null value for a particular type. This essentially
    /// just emits a zero'd out value for the type.
    fn const_null(&self, ty: Self::Type) -> Self::Value;

    /// Emit a constant boolean value.
    fn const_bool(&self, val: bool) -> Self::Value;

    /// Emit a constant `u8` value.
    fn const_u8(&self, i: u8) -> Self::Value;

    /// Emit a constant `i8` value.
    fn const_i8(&self, i: i8) -> Self::Value;

    /// Emit a constant `u16` value.
    fn const_u16(&self, i: i16) -> Self::Value;

    /// Emit a constant `i16` value.
    fn const_i16(&self, i: i16) -> Self::Value;

    /// Emit a constant `u32` value.    
    fn const_u32(&self, i: u32) -> Self::Value;

    /// Emit a constant `i32` value.
    fn const_i32(&self, i: i32) -> Self::Value;

    /// Emit a constant `u64` value.
    fn const_u64(&self, i: u64) -> Self::Value;

    /// Emit a constant `i64` value.
    fn const_i64(&self, i: i64) -> Self::Value;

    /// Emit a constant `u128` value.
    fn const_u128(&self, i: u128) -> Self::Value;

    /// Emit a constant `i128` value.
    fn const_i128(&self, i: i128) -> Self::Value;

    /// Emit a constant unsigned integer with a specified size.
    fn const_uint(&self, ty: Self::Type, value: u64) -> Self::Value;

    /// Emit a large integer constant of a particular type. This
    /// is a common function to emit unsigned interger types.
    fn const_uint_big(&self, ty: Self::Type, i: u128) -> Self::Value;

    /// Emit a constant signed integer with a specific size.
    fn const_int(&self, ty: Self::Type, value: i64) -> Self::Value;

    /// Emit a constant `usize` value.
    fn const_usize(&self, i: u64) -> Self::Value;

    /// Emit a constant float value.
    fn const_float(&self, t: Self::Type, val: f64) -> Self::Value;

    /// Emit a constant string value. This will return a  
    /// pointer value to the string characters, and a
    /// second value for the length of the string. Essentially,
    /// this mimics the following structure:
    /// ```ignore
    /// str := struct {
    ///     raw: &char, // <--- first value
    ///     len: usize, // <--- second value
    /// }
    /// ```
    fn const_str(&self, s: &str) -> (Self::Value, Self::Value);

    /// Attempt to convert a constant value into a `u128` value. If
    /// the conversion fails, then [`None`] is returned.
    fn const_to_optional_u128(&self, val: Self::Value, sign_extend: bool) -> Option<u128>;
}
