//! Implements all of the constant building methods.
use hash_codegen::traits::{constants::ConstValueBuilderMethods, ty::BuildTypeMethods};
use hash_ir::ir::Const;
use hash_source::constant::InternedStr;
use hash_target::{abi::Scalar, data_layout::HasDataLayout};
use inkwell::{
    types::BasicTypeEnum,
    values::{AnyValueEnum, AsValueRef},
};

use super::context::CodeGenCtx;

impl<'b> ConstValueBuilderMethods<'b> for CodeGenCtx<'b> {
    fn const_undef(&self, ty: Self::Type) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        match ty {
            BasicTypeEnum::ArrayType(ty) => ty.get_undef().into(),
            BasicTypeEnum::FloatType(ty) => ty.get_undef().into(),
            BasicTypeEnum::IntType(ty) => ty.get_undef().into(),
            BasicTypeEnum::PointerType(ty) => ty.get_undef().into(),
            BasicTypeEnum::StructType(ty) => ty.get_undef().into(),
            BasicTypeEnum::VectorType(ty) => ty.get_undef().into(),
        }
    }

    fn const_null(&self, ty: Self::Type) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.const_zero().into()
    }

    fn const_bool(&self, value: bool) -> Self::Value {
        self.const_uint(self.type_i1(), value as u64)
    }

    fn const_u8(&self, value: u8) -> Self::Value {
        self.const_uint(self.type_i8(), value as u64)
    }

    fn const_i8(&self, value: i8) -> Self::Value {
        self.const_int(self.type_i8(), value as i64)
    }

    fn const_u16(&self, value: i16) -> Self::Value {
        self.const_uint(self.type_i16(), value as u64)
    }

    fn const_i16(&self, i: i16) -> Self::Value {
        self.const_int(self.type_i16(), i as i64)
    }

    fn const_u32(&self, i: u32) -> Self::Value {
        self.const_uint(self.type_i32(), i as u64)
    }

    fn const_i32(&self, i: i32) -> Self::Value {
        self.const_int(self.type_i32(), i as i64)
    }

    fn const_u64(&self, i: u64) -> Self::Value {
        self.const_uint(self.type_i64(), i)
    }

    fn const_i64(&self, i: i64) -> Self::Value {
        self.const_int(self.type_i64(), i)
    }

    fn const_u128(&self, i: u128) -> Self::Value {
        self.const_uint_big(self.type_i128(), i)
    }

    fn const_uint(&self, ty: Self::Type, value: u64) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.into_int_type().const_int(value, false).into()
    }

    fn const_uint_big(&self, ty: Self::Type, value: u128) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();

        let words = [value as u64, (value >> 64) as u64];
        ty.into_int_type().const_int_arbitrary_precision(&words).into()
    }

    fn const_int(&self, ty: Self::Type, value: i64) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.into_int_type().const_int(value as u64, true).into()
    }

    fn const_usize(&self, value: u64) -> Self::Value {
        let bit_size = self.data_layout().pointer_size.bits();

        if bit_size < 64 {
            debug_assert!(value < (1 << bit_size));
        }

        self.const_uint(self.size_ty, value)
    }

    fn const_float(&self, ty: Self::Type, val: f64) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.into_float_type().const_float(val).into()
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
        if let AnyValueEnum::IntValue(val) = value && val.is_constant_int() {
            let value = val.get_type().get_bit_width();
            if value > 128 {
                return None;
            }

            // @@Hack: this doesn't properly handle the full range of i128 values, however]
            // Inkwell doesn't support arbitrary precision integers, so we can't do much better...
            // unless we @@PatchInkwell
            if sign_extend {
                val.get_sign_extended_constant().map(|v| {
                    // upcast to i128, and then convert into u128
                    unsafe { std::mem::transmute::<i128, u128>(v as i128) }
                })
            } else {
                val.get_zero_extended_constant().map(|v| v as u128)
            }
        } else {
            None
        }
    }

    fn const_to_optional_uint(&self, value: Self::Value) -> Option<u64> {
        if let AnyValueEnum::IntValue(val) = value && val.is_constant_int() {
            val.get_zero_extended_constant()
        } else {
            None
        }
    }
}
