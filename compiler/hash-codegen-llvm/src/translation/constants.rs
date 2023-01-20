//! Implements all of the constant building methods.
use hash_codegen::traits::constants::BuildConstValueMethods;
use hash_ir::ir::Const;
use hash_source::constant::InternedStr;
use hash_target::abi::Scalar;

use super::context::CodeGenCtx;

impl<'b> BuildConstValueMethods<'b> for CodeGenCtx<'b> {
    fn const_undef(&self, ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_null(&self, ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_bool(&self, val: bool) -> Self::Value {
        todo!()
    }

    fn const_u8(&self, i: u8) -> Self::Value {
        todo!()
    }

    fn const_i8(&self, i: i8) -> Self::Value {
        todo!()
    }

    fn const_u16(&self, i: i16) -> Self::Value {
        todo!()
    }

    fn const_i16(&self, i: i16) -> Self::Value {
        todo!()
    }

    fn const_u32(&self, i: u32) -> Self::Value {
        todo!()
    }

    fn const_i32(&self, i: i32) -> Self::Value {
        todo!()
    }

    fn const_u64(&self, i: u64) -> Self::Value {
        todo!()
    }

    fn const_i64(&self, i: i64) -> Self::Value {
        todo!()
    }

    fn const_u128(&self, i: u128) -> Self::Value {
        todo!()
    }

    fn const_i128(&self, i: i128) -> Self::Value {
        todo!()
    }

    fn const_uint(&self, ty: Self::Type, value: u64) -> Self::Value {
        todo!()
    }

    fn const_uint_big(&self, ty: Self::Type, i: u128) -> Self::Value {
        todo!()
    }

    fn const_int(&self, ty: Self::Type, value: i64) -> Self::Value {
        todo!()
    }

    fn const_usize(&self, i: u64) -> Self::Value {
        todo!()
    }

    fn const_float(&self, t: Self::Type, val: f64) -> Self::Value {
        todo!()
    }

    fn const_str(&self, s: &str) -> (Self::Value, Self::Value) {
        todo!()
    }

    fn const_interned_str(&self, s: InternedStr) -> (Self::Value, Self::Value) {
        todo!()
    }

    fn const_scalar_value(&self, const_value: Const, abi: Scalar, ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_to_optional_u128(&self, value: Self::Value, sign_extend: bool) -> Option<u128> {
        todo!()
    }

    fn const_to_optional_uint(&self, value: Self::Value) -> Option<u64> {
        todo!()
    }
}
