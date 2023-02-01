//! Implements the [BuildIntrinsicCallMethods] trait for [Builder].

use hash_codegen::{
    abi::FnAbi,
    lower::{operands::OperandRef, place::PlaceRef},
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods,
        intrinsics::IntrinsicBuilderMethods, ty::TypeBuilderMethods, BackendTypes,
    },
};
use hash_ir::ty::{IrTy, IrTyId};
use hash_source::identifier::{Identifier, IDENTS};
use hash_utils::store::CloneStore;
use inkwell::values::{AnyValueEnum, UnnamedAddress};

use super::Builder;

impl<'b, 'm> Builder<'_, 'b, 'm> {
    /// Call an intrinsic function with the specified arguments.
    pub(crate) fn call_intrinsic(
        &mut self,
        name: &str,
        args: &[AnyValueEnum<'m>],
    ) -> <Self as BackendTypes>::Value {
        let func = self.get_intrinsic_function(name);
        self.call(func, args, None)
    }

    /// Get an intrinsic function type and function pointer value
    /// for the given intrinsic name.
    pub(crate) fn get_intrinsic_function(&self, name: &str) -> <Self as BackendTypes>::Function {
        if let Some(intrinsic) = self.intrinsics.borrow().get(name).cloned() {
            return intrinsic;
        }

        self.declare_intrinsic(name).unwrap_or_else(|| {
            panic!("unable to resolve intrinsic `{name}`");
        })
    }

    pub(crate) fn declare_intrinsic(&self, name: &str) -> Option<<Self as BackendTypes>::Function> {
        // This macro is used to define the intrinsic based on the function name.
        // If the name of the intrinsic is equal to the specified value, then this
        // type and function pointer value will be returned.
        macro_rules! intrinsic_on {
            ($name:literal, fn() -> $ret:expr) => (
                if name == $name {
                    return Some(self.insert_intrinsic($name, &[], $ret));
                }
            );
            ($name:expr, fn($($arg:expr),*) -> $ret:expr) => (
                if name == $name {
                    return Some(self.insert_intrinsic($name, &[$($arg),*], $ret));
                }
            );
        }

        // Create a struct type which is used as the return type for some
        // intrinsics
        macro_rules! struct_ty {
            ($($field_ty:expr),*) => (self.type_struct( &[$($field_ty),*], false))
        }

        // Declare all of the types that might occur within the intrinsic.
        let _ptr = self.type_i8p();
        let void = self.type_void();
        let bool = self.type_i1();
        let i8 = self.type_i8();
        let i16 = self.type_i16();
        let i32 = self.type_i32();
        let i64 = self.type_i64();
        let i128 = self.type_i128();
        let _isize = self.type_isize();
        let f32 = self.type_f32();
        let f64 = self.type_f64();
        let _metadata = self.type_metadata();

        // Declare all of the intrinsics that we support.

        // Floating point to integer intrinsics
        intrinsic_on!("llvm.fptosi.sat.i8.f32", fn(f32) -> i8);
        intrinsic_on!("llvm.fptosi.sat.i16.f32", fn(f32) -> i16);
        intrinsic_on!("llvm.fptosi.sat.i32.f32", fn(f32) -> i32);
        intrinsic_on!("llvm.fptosi.sat.i64.f32", fn(f32) -> i64);
        intrinsic_on!("llvm.fptosi.sat.i128.f32", fn(f32) -> i128);
        intrinsic_on!("llvm.fptosi.sat.i8.f64", fn(f64) -> i8);
        intrinsic_on!("llvm.fptosi.sat.i16.f64", fn(f64) -> i16);
        intrinsic_on!("llvm.fptosi.sat.i32.f64", fn(f64) -> i32);
        intrinsic_on!("llvm.fptosi.sat.i64.f64", fn(f64) -> i64);
        intrinsic_on!("llvm.fptosi.sat.i128.f64", fn(f64) -> i128);
        intrinsic_on!("llvm.fptoui.sat.i8.f32", fn(f32) -> i8);
        intrinsic_on!("llvm.fptoui.sat.i16.f32", fn(f32) -> i16);
        intrinsic_on!("llvm.fptoui.sat.i32.f32", fn(f32) -> i32);
        intrinsic_on!("llvm.fptoui.sat.i64.f32", fn(f32) -> i64);
        intrinsic_on!("llvm.fptoui.sat.i128.f32", fn(f32) -> i128);
        intrinsic_on!("llvm.fptoui.sat.i8.f64", fn(f64) -> i8);
        intrinsic_on!("llvm.fptoui.sat.i16.f64", fn(f64) -> i16);
        intrinsic_on!("llvm.fptoui.sat.i32.f64", fn(f64) -> i32);
        intrinsic_on!("llvm.fptoui.sat.i64.f64", fn(f64) -> i64);
        intrinsic_on!("llvm.fptoui.sat.i128.f64", fn(f64) -> i128);

        // Abort intrinsic
        intrinsic_on!("llvm.trap", fn() -> void);

        intrinsic_on!("llvm.powi.f32", fn(f32, i32) -> f32);
        intrinsic_on!("llvm.powi.f64", fn(f64, i32) -> f64);

        intrinsic_on!("llvm.pow.f32", fn(f32, f32) -> f32);
        intrinsic_on!("llvm.pow.f64", fn(f64, f64) -> f64);

        intrinsic_on!("llvm.sqrt.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.sqrt.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.sin.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.sin.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.cos.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.cos.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.exp.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.exp.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.exp2.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.exp2.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.log.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.log.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.log10.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.log10.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.log2.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.log2.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.fma.f32", fn(f32, f32, f32) -> f32);
        intrinsic_on!("llvm.fma.f64", fn(f64, f64, f64) -> f64);

        intrinsic_on!("llvm.fabs.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.fabs.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.minnum.f32", fn(f32, f32) -> f32);
        intrinsic_on!("llvm.minnum.f64", fn(f64, f64) -> f64);
        intrinsic_on!("llvm.maxnum.f32", fn(f32, f32) -> f32);
        intrinsic_on!("llvm.maxnum.f64", fn(f64, f64) -> f64);

        intrinsic_on!("llvm.floor.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.floor.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.ceil.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.ceil.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.trunc.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.trunc.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.copysign.f32", fn(f32, f32) -> f32);
        intrinsic_on!("llvm.copysign.f64", fn(f64, f64) -> f64);
        intrinsic_on!("llvm.round.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.round.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.rint.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.rint.f64", fn(f64) -> f64);
        intrinsic_on!("llvm.nearbyint.f32", fn(f32) -> f32);
        intrinsic_on!("llvm.nearbyint.f64", fn(f64) -> f64);

        intrinsic_on!("llvm.ctpop.i8", fn(i8) -> i8);
        intrinsic_on!("llvm.ctpop.i16", fn(i16) -> i16);
        intrinsic_on!("llvm.ctpop.i32", fn(i32) -> i32);
        intrinsic_on!("llvm.ctpop.i64", fn(i64) -> i64);
        intrinsic_on!("llvm.ctpop.i128", fn(i128) -> i128);

        intrinsic_on!("llvm.ctlz.i8", fn(i8, bool) -> i8);
        intrinsic_on!("llvm.ctlz.i16", fn(i16, bool) -> i16);
        intrinsic_on!("llvm.ctlz.i32", fn(i32, bool) -> i32);
        intrinsic_on!("llvm.ctlz.i64", fn(i64, bool) -> i64);
        intrinsic_on!("llvm.ctlz.i128", fn(i128, bool) -> i128);

        intrinsic_on!("llvm.cttz.i8", fn(i8, bool) -> i8);
        intrinsic_on!("llvm.cttz.i16", fn(i16, bool) -> i16);
        intrinsic_on!("llvm.cttz.i32", fn(i32, bool) -> i32);
        intrinsic_on!("llvm.cttz.i64", fn(i64, bool) -> i64);
        intrinsic_on!("llvm.cttz.i128", fn(i128, bool) -> i128);

        intrinsic_on!("llvm.bswap.i16", fn(i16) -> i16);
        intrinsic_on!("llvm.bswap.i32", fn(i32) -> i32);
        intrinsic_on!("llvm.bswap.i64", fn(i64) -> i64);
        intrinsic_on!("llvm.bswap.i128", fn(i128) -> i128);

        intrinsic_on!("llvm.bitreverse.i8", fn(i8) -> i8);
        intrinsic_on!("llvm.bitreverse.i16", fn(i16) -> i16);
        intrinsic_on!("llvm.bitreverse.i32", fn(i32) -> i32);
        intrinsic_on!("llvm.bitreverse.i64", fn(i64) -> i64);
        intrinsic_on!("llvm.bitreverse.i128", fn(i128) -> i128);

        intrinsic_on!("llvm.fshl.i8", fn(i8, i8, i8) -> i8);
        intrinsic_on!("llvm.fshl.i16", fn(i16, i16, i16) -> i16);
        intrinsic_on!("llvm.fshl.i32", fn(i32, i32, i32) -> i32);
        intrinsic_on!("llvm.fshl.i64", fn(i64, i64, i64) -> i64);
        intrinsic_on!("llvm.fshl.i128", fn(i128, i128, i128) -> i128);

        intrinsic_on!("llvm.fshr.i8", fn(i8, i8, i8) -> i8);
        intrinsic_on!("llvm.fshr.i16", fn(i16, i16, i16) -> i16);
        intrinsic_on!("llvm.fshr.i32", fn(i32, i32, i32) -> i32);
        intrinsic_on!("llvm.fshr.i64", fn(i64, i64, i64) -> i64);
        intrinsic_on!("llvm.fshr.i128", fn(i128, i128, i128) -> i128);

        // Overflow intrinsics

        intrinsic_on!("llvm.sadd.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.sadd.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.sadd.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.sadd.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.sadd.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        intrinsic_on!("llvm.uadd.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.uadd.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.uadd.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.uadd.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.uadd.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        intrinsic_on!("llvm.ssub.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.ssub.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.ssub.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.ssub.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.ssub.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        intrinsic_on!("llvm.usub.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.usub.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.usub.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.usub.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.usub.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        intrinsic_on!("llvm.smul.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.smul.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.smul.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.smul.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.smul.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        intrinsic_on!("llvm.umul.with.overflow.i8", fn(i8, i8) -> struct_ty! {i8, bool});
        intrinsic_on!("llvm.umul.with.overflow.i16", fn(i16, i16) -> struct_ty! {i16, bool});
        intrinsic_on!("llvm.umul.with.overflow.i32", fn(i32, i32) -> struct_ty! {i32, bool});
        intrinsic_on!("llvm.umul.with.overflow.i64", fn(i64, i64) -> struct_ty! {i64, bool});
        intrinsic_on!("llvm.umul.with.overflow.i128", fn(i128, i128) -> struct_ty! {i128, bool});

        None
    }

    /// Function that is used to insert an intrinsic into the current module,
    /// essentially declaring it for use.
    fn insert_intrinsic(
        &self,
        name: &'static str,
        args: &[<Self as BackendTypes>::Type],
        return_ty: <Self as BackendTypes>::Type,
    ) -> <Self as BackendTypes>::Function {
        let func_ty = self.type_function(args, return_ty);
        let func = self.declare_c_fn(name, UnnamedAddress::None, func_ty);

        // Now we add the function into the "intrinsics" map in order to
        // avoid re-declaring the function or re-resolving the function.
        self.intrinsics.borrow_mut().insert(name, func);
        func
    }

    /// Attempt to resolve an intrinsic function that is "simple" in
    /// nature. The notion of "simple" implies that only a call needs
    /// to be generated for this intrinsic function, all others are
    /// considered "special" and require additional steps to generate
    /// code for.
    fn get_simple_intrinsic(&self, name: Identifier) -> Option<<Self as BackendTypes>::Function> {
        let name = match name {
            i if i == IDENTS.sqrt_f32 => "llvm.sqrt.f32",
            i if i == IDENTS.sqrt_f64 => "llvm.sqrt.f64",
            i if i == IDENTS.powi_f32 => "llvm.powi.f32",
            i if i == IDENTS.powi_f64 => "llvm.powi.f64",
            i if i == IDENTS.sin_f32 => "llvm.sin.f32",
            i if i == IDENTS.sin_f64 => "llvm.sin.f64",
            i if i == IDENTS.cos_f32 => "llvm.cos.f32",
            i if i == IDENTS.cos_f64 => "llvm.cos.f64",
            i if i == IDENTS.pow_f32 => "llvm.pow.f32",
            i if i == IDENTS.pow_f64 => "llvm.pow.f64",
            i if i == IDENTS.exp_f32 => "llvm.exp.f32",
            i if i == IDENTS.exp_f64 => "llvm.exp.f64",
            i if i == IDENTS.exp2_f32 => "llvm.exp2.f32",
            i if i == IDENTS.exp2_f64 => "llvm.exp2.f64",
            i if i == IDENTS.log_f32 => "llvm.log.f32",
            i if i == IDENTS.log_f64 => "llvm.log.f64",
            i if i == IDENTS.log10_f32 => "llvm.log10.f32",
            i if i == IDENTS.log10_f64 => "llvm.log10.f64",
            i if i == IDENTS.log2_f32 => "llvm.log2.f32",
            i if i == IDENTS.log2_f64 => "llvm.log2.f64",
            i if i == IDENTS.fma_f32 => "llvm.fma.f32",
            i if i == IDENTS.fma_f64 => "llvm.fma.f64",
            i if i == IDENTS.fabs_f32 => "llvm.fabs.f32",
            i if i == IDENTS.fabs_f64 => "llvm.fabs.f64",
            _ => return None,
        };

        Some(self.get_intrinsic_function(name))
    }
}

impl<'b, 'm> IntrinsicBuilderMethods<'b> for Builder<'_, 'b, 'm> {
    fn codegen_intrinsic_call(
        &mut self,
        ty: IrTyId,
        fn_abi: &FnAbi,
        args: &[Self::Value],
        result: Self::Value,
    ) {
        // firstly we try to resolve the intrinsic function via the "simple" variants,
        // or otherwise we might need to perform additional steps to generate code for
        // the intrinsics.
        //
        // However, since we haven't formally defined any "special" intrinsics yet, we
        // don't expect for the resolution to fail.

        let IrTy::Fn { instance, .. } = self.ir_ctx.tys().get(ty) else {
            panic!("unable to resolve intrinsic function type");
        };
        let name = self.ir_ctx.instances().name_of(instance);

        let result_ref = PlaceRef::new(self, result, fn_abi.ret_abi.info);

        // if we can simply resolve the intrinsic then we can just call it directly...
        let value = if let Some(intrinsic) = self.get_simple_intrinsic(name) {
            self.call(intrinsic, args, None)
        } else {
            // @@Todo: deal with more "non-trivial" intrinsics
            unimplemented!("intrinsic function `{name}` is not trivial")
        };

        // If the result isn't ignored, then we write the result into the provided
        // operand place.
        if !fn_abi.ret_abi.is_ignored() {
            OperandRef::from_immediate_value_or_scalar_pair(self, value, result_ref.info)
                .value
                .store(self, result_ref);
        }
    }

    fn codegen_abort_intrinsic(&mut self) {
        self.call_intrinsic("llvm.trap", &[]);
    }

    fn codegen_expect_intrinsic(&mut self, value: Self::Value, expected: bool) -> Self::Value {
        let expected = self.const_bool(expected);
        self.call_intrinsic("llvm.expect.i1", &[value, expected])
    }
}
