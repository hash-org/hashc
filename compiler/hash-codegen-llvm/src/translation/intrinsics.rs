//! Implements the [BuildIntrinsicCallMethods] trait for [Builder].

use hash_codegen::traits::{
    builder::BlockBuilderMethods, intrinsics::BuildIntrinsicCallMethods, BackendTypes,
};
use inkwell::values::AnyValueEnum;

use super::Builder;

impl<'b> Builder<'b> {
    /// Call an intrinsic function with the specified arguments.
    pub(crate) fn call_intrinsic(
        &mut self,
        name: &str,
        args: &[AnyValueEnum<'b>],
    ) -> <Self as BackendTypes>::Value {
        let (ty, func) = self.get_intrinsic_function(name);
        self.call(ty, None, func, args)
    }

    /// Get an intrinsic function type and function pointer value
    /// for the given intrinsic name.
    pub(crate) fn get_intrinsic_function(
        &self,
        name: &str,
    ) -> (<Self as BackendTypes>::Type, <Self as BackendTypes>::Value) {
        todo!()
    }

    fn insert_instruction(
        &self,
        name: &str,
        args: &[<Self as BackendTypes>::Type],
        return_ty: <Self as BackendTypes>::Type,
    ) -> (<Self as BackendTypes>::Type, <Self as BackendTypes>::Value) {
        todo!()
    }
}

impl<'b> BuildIntrinsicCallMethods<'b> for Builder<'b> {
    fn codegen_intrinsic_call(
        &self,
        ty: hash_ir::ty::IrTyId,
        args: &[Self::Value],
        result: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn codegen_abort_intrinsic(&mut self) {
        todo!()
    }

    fn codegen_expect_intrinsic(&mut self, value: Self::Value, expected: bool) -> Self::Value {
        todo!()
    }
}
