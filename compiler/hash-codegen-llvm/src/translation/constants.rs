//! Implements all of the constant building methods.
use hash_codegen::{
    target::{
        abi::{Scalar, ScalarKind},
        data_layout::HasDataLayout,
    },
    traits::{constants::ConstValueBuilderMethods, ty::TypeBuilderMethods},
};
use hash_source::constant::{self, AllocId, AllocRange, Size};
use hash_storage::store::statics::StoreId;
use inkwell::{
    module::Linkage,
    types::{AsTypeRef, BasicTypeEnum},
    values::{AnyValue, AnyValueEnum, AsValueRef, BasicValueEnum},
};
use llvm_sys::core as llvm;

use crate::ctx::CodeGenCtx;

impl<'b> ConstValueBuilderMethods<'b> for CodeGenCtx<'b, '_> {
    fn const_undef(&self, ty: Self::Type) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        match ty {
            BasicTypeEnum::ArrayType(ty) => ty.get_undef().into(),
            BasicTypeEnum::FloatType(ty) => ty.get_undef().into(),
            BasicTypeEnum::IntType(ty) => ty.get_undef().into(),
            BasicTypeEnum::PointerType(ty) => ty.get_undef().into(),
            BasicTypeEnum::StructType(ty) => ty.get_undef().into(),
            BasicTypeEnum::VectorType(ty) => ty.get_undef().into(),
            BasicTypeEnum::ScalableVectorType(ty) => ty.get_undef().into(),
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
    fn const_str(&self, s: AllocId) -> (Self::Value, Self::Value) {
        let value = s.to_str();
        let str_len = value.len();

        let mut str_consts = self.str_consts.borrow_mut();
        let global_str = str_consts.entry(s).or_insert_with(|| {
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
            global
        });

        (global_str.as_any_value_enum(), self.const_usize(str_len as u64))
    }

    fn const_struct(&self, values: &[Self::Value], packed: bool) -> Self::Value {
        let values: Vec<BasicValueEnum> = values.iter().map(|v| (*v).try_into().unwrap()).collect();

        self.ll_ctx.const_struct(&values, packed).as_any_value_enum()
    }

    fn const_bytes(&self, bytes: &[u8]) -> Self::Value {
        // ##Hack: we pretend that this is a null terminated string, just to emit
        // some bytes. Ultimately, it doesn't really matter that it is a constant
        // string since it will just be casted into whatever the type is, this
        // is just needed to store some bytes.
        self.ll_ctx.const_string(bytes, /* null_terminated: */ true).as_any_value_enum()
    }

    fn const_scalar_value(
        &self,
        scalar: constant::Scalar,
        abi: Scalar,
        ty: Self::Type,
    ) -> Self::Value {
        let size = abi.size(self);
        let bits = if abi.is_bool() { 1 } else { size.bits() };

        let data = scalar.assert_bits(size);
        let value = self.const_uint_big(self.type_ix(bits), data);

        // @@Todo: we need to deal with the case that this scalar is
        // actually a pointer. We have to emit different code based on
        // the type of the refereee.
        if matches!(abi.kind(), ScalarKind::Pointer(_)) {
            unsafe {
                AnyValueEnum::new(llvm::LLVMConstIntToPtr(value.as_value_ref(), ty.as_type_ref()))
            }
        } else {
            self.const_bitcast(value, ty)
        }
    }

    fn const_data_from_alloc(&self, alloc: constant::AllocId) -> Self::Value {
        alloc.map(|allocation| {
            let mut values = vec![];

            // For now, we can just emit the `bytes` that are stored
            // in the allocation. We can do this because the way constant
            // allocations are constructed is identical to the way that
            // data layouts are constructed.
            let alloc_range = AllocRange::new(Size::ZERO, allocation.size());
            values.push(self.const_bytes(allocation.read_bytes(alloc_range)));

            self.const_struct(&values, false)
        })
    }

    fn const_ptr_byte_offset(&self, base: Self::Value, offset: Size) -> Self::Value {
        let ptr = base.into_pointer_value();

        unsafe {
            AnyValueEnum::new(llvm::LLVMConstInBoundsGEP2(
                self.type_i8().as_type_ref(),
                ptr.as_value_ref(),
                &mut self.const_usize(offset.bytes()).as_value_ref(),
                1,
            ))
        }
    }

    fn const_bitcast(&self, val: Self::Value, ty: Self::Type) -> Self::Value {
        unsafe { AnyValueEnum::new(llvm::LLVMConstBitCast(val.as_value_ref(), ty.as_type_ref())) }
    }

    fn const_to_optional_u128(&self, value: Self::Value, sign_extend: bool) -> Option<u128> {
        if let AnyValueEnum::IntValue(val) = value
            && val.is_constant_int()
        {
            let value = val.get_type().get_bit_width();
            if value > 128 {
                return None;
            }

            // ##Hack: this doesn't properly handle the full range of i128 values, however
            // Inkwell doesn't support arbitrary precision integers, so we can't do much
            // better... unless we @@PatchInkwell
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
        if let AnyValueEnum::IntValue(val) = value
            && val.is_constant_int()
        {
            val.get_zero_extended_constant()
        } else {
            None
        }
    }
}
