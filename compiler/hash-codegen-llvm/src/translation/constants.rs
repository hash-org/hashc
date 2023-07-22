//! Implements all of the constant building methods.
use hash_codegen::{
    target::{abi::Scalar, data_layout::HasDataLayout},
    traits::{constants::ConstValueBuilderMethods, layout::LayoutMethods, ty::TypeBuilderMethods},
};
use hash_ir::{ir::Const, ty::COMMON_IR_TYS};
use hash_source::constant::{InternedStr, CONSTANT_MAP};
use inkwell::{module::Linkage, types::BasicTypeEnum, values::AnyValueEnum};

use super::ty::ExtendedTyBuilderMethods;
use crate::ctx::CodeGenCtx;

impl<'b, 'm> ConstValueBuilderMethods<'b> for CodeGenCtx<'b, 'm> {
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

        self.const_uint(self.size_ty.into(), value)
    }

    fn const_float(&self, ty: Self::Type, val: f64) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.into_float_type().const_float(val).into()
    }

    /// Create a global constant value for the [InternedStr].
    fn const_str(&self, s: InternedStr) -> (Self::Value, Self::Value) {
        let value: &str = s.into();
        let str_len = value.len();

        let mut str_consts = self.str_consts.borrow_mut();
        let (_, global_str) = str_consts.raw_entry_mut().from_key(&s).or_insert_with(|| {
            let value: &str = s.into();

            let str = self.ll_ctx.const_string(value.as_bytes(), false);

            // Here we essentially create a global with a new name...
            let const_name = self.generate_local_symbol_name("str");
            let global = self
                .declare_global(&const_name, str.get_type().into())
                .unwrap_or_else(|| panic!("constant string global symbol already defined"));

            global.set_initializer(&str);
            global.set_constant(true);

            // Internal specifies that the value is a "local" symbol in the
            // object file, i.e. a `static`.
            //
            // Ref: <https://llvm.org/docs/LangRef.html#linkage-types>
            global.set_linkage(Linkage::Internal);
            (s, global)
        });

        let byte_slice_ty = COMMON_IR_TYS.byte_slice;
        let ptr = global_str.as_pointer_value().const_cast(
            self.type_ptr_to(self.layout_of(byte_slice_ty).llvm_ty(self)).into_pointer_type(),
        );

        (ptr.into(), self.const_usize(str_len as u64))
    }

    fn const_scalar_value(&self, const_value: Const, _abi: Scalar, ty: Self::Type) -> Self::Value {
        match const_value {
            // This is handled at the translation layer, `const_scalar_value` should not be called
            // on a ZST.
            Const::Zero(_) => unreachable!("`const_scalar_value` should not be called on a ZST"),
            Const::Bool(val) => self.const_bool(val),
            Const::Char(ch) => self.const_u32(ch as u32),
            Const::Int(interned_int) => {
                let const_int = CONSTANT_MAP.lookup_int(interned_int);

                // Convert the constant into a u128 and then emit the
                // correct LLVM constant for it.
                const_int
                    .value
                    .as_u128()
                    .map(|value| self.const_uint_big(ty, value))
                    .unwrap_or_else(|| {
                        // @@Todo: deal with bigints...
                        unimplemented!()
                    })
            }
            Const::Float(interned_float) => {
                self.const_float(ty, CONSTANT_MAP.lookup_float(interned_float).as_f64())
            }
            Const::Str(str) => self.const_str(str).0,
        }
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
