//! Implements the [BuildIntrinsicCallMethods] trait for [Builder].

use hash_codegen::traits::intrinsics::BuildIntrinsicCallMethods;

use super::Builder;

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
