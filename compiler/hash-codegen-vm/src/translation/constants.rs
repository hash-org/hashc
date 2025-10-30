use hash_codegen::traits::constants::ConstValueBuilderMethods;

use crate::ctx::Ctx;

impl<'b> ConstValueBuilderMethods<'b> for Ctx<'b> {
    fn const_undef(&self, _ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_null(&self, _ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_bool(&self, _val: bool) -> Self::Value {
        todo!()
    }

    fn const_u8(&self, _i: u8) -> Self::Value {
        todo!()
    }

    fn const_i8(&self, _i: i8) -> Self::Value {
        todo!()
    }

    fn const_u16(&self, _i: i16) -> Self::Value {
        todo!()
    }

    fn const_i16(&self, _i: i16) -> Self::Value {
        todo!()
    }

    fn const_u32(&self, _i: u32) -> Self::Value {
        todo!()
    }

    fn const_i32(&self, _i: i32) -> Self::Value {
        todo!()
    }

    fn const_u64(&self, _i: u64) -> Self::Value {
        todo!()
    }

    fn const_i64(&self, _i: i64) -> Self::Value {
        todo!()
    }

    fn const_u128(&self, _i: u128) -> Self::Value {
        todo!()
    }

    fn const_uint(&self, _ty: Self::Type, _value: u64) -> Self::Value {
        todo!()
    }

    fn const_uint_big(&self, _ty: Self::Type, _i: u128) -> Self::Value {
        todo!()
    }

    fn const_int(&self, _ty: Self::Type, _value: i64) -> Self::Value {
        todo!()
    }

    fn const_usize(&self, _i: u64) -> Self::Value {
        todo!()
    }

    fn const_float(&self, _t: Self::Type, _val: f64) -> Self::Value {
        todo!()
    }

    fn const_str(&self, _s: hash_ir::ir::AllocId) -> (Self::Value, Self::Value) {
        todo!()
    }

    fn const_struct(&self, _values: &[Self::Value], _packed: bool) -> Self::Value {
        todo!()
    }

    fn const_bytes(&self, _bytes: &[u8]) -> Self::Value {
        todo!()
    }

    fn const_scalar_value(
        &self,
        _scalar: hash_ir::ir::Scalar,
        _abi: hash_codegen::target::abi::Scalar,
        _ty: Self::Type,
    ) -> Self::Value {
        todo!()
    }

    fn const_data_from_alloc(&self, _alloc: hash_ir::ir::AllocId) -> Self::Value {
        todo!()
    }

    fn const_ptr_byte_offset(&self, _base: Self::Value, _offset: hash_source::Size) -> Self::Value {
        todo!()
    }

    fn const_bitcast(&self, _val: Self::Value, _ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn const_to_optional_u128(&self, _value: Self::Value, _sign_extend: bool) -> Option<u128> {
        todo!()
    }

    fn const_to_optional_uint(&self, _value: Self::Value) -> Option<u64> {
        todo!()
    }
}
