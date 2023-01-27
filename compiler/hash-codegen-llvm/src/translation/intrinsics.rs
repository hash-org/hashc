//! Implements the [BuildIntrinsicCallMethods] trait for [Builder].

use hash_codegen::{
    abi::FnAbi,
    lower::{operands::OperandRef, place::PlaceRef},
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods,
        intrinsics::IntrinsicBuilderMethods, BackendTypes,
    },
};
use hash_ir::ty::{IrTy, IrTyId};
use hash_utils::store::CloneStore;
use inkwell::values::AnyValueEnum;

use super::Builder;

impl<'b> Builder<'b> {
    /// Call an intrinsic function with the specified arguments.
    pub(crate) fn call_intrinsic(
        &mut self,
        name: &str,
        args: &[AnyValueEnum<'b>],
    ) -> <Self as BackendTypes>::Value {
        let Some((ty, func)) = self.get_intrinsic_function(name) else {
            panic!("unable to resolve intrinsic `{name}`");
        };

        self.call(ty, None, func, args)
    }

    /// Get an intrinsic function type and function pointer value
    /// for the given intrinsic name.
    pub(crate) fn get_intrinsic_function(
        &self,
        name: &str,
    ) -> Option<(<Self as BackendTypes>::Type, <Self as BackendTypes>::Value)> {
        todo!()
    }

    fn insert_intrinsic(
        &self,
        name: &str,
        args: &[<Self as BackendTypes>::Type],
        return_ty: <Self as BackendTypes>::Type,
    ) -> (<Self as BackendTypes>::Type, <Self as BackendTypes>::Value) {
        todo!()
    }
}

impl<'b> IntrinsicBuilderMethods<'b> for Builder<'b> {
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

        let IrTy::Fn { name: Some(name), instance, params, return_ty } = self.ir_ctx.tys().get(ty) else {
            panic!("unable to resolve intrinsic function type");
        };

        let result_ref = PlaceRef::new(self, result, fn_abi.ret_abi.info);

        // if we can simply resolve the intrinsic then we can just call it directly...
        let value = if let Some((ty, value)) = self.get_intrinsic_function(name.into()) {
            self.call(ty, None, value, args)
        } else {
            // @@Todo: deal with more "non-trivial" intrinsics
            panic!("unable to resolve intrinsic function: {name}")
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
