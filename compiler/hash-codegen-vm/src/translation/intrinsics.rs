//! Implements the [BuildIntrinsicCallMethods] trait for [Builder].

use hash_codegen::{abi::FnAbi, traits::intrinsics::IntrinsicBuilderMethods};
use hash_ir::ty::ReprTyId;

use super::VMBuilder;

impl<'b> IntrinsicBuilderMethods<'b> for VMBuilder<'b> {
    fn codegen_intrinsic_call(
        &mut self,
        _ty: ReprTyId,
        _fn_abi: &FnAbi,
        _args: &[Self::Value],
        _result: Self::Value,
    ) {
        unimplemented!()
    }

    fn codegen_abort_intrinsic(&mut self) {
        unimplemented!()
    }

    fn codegen_expect_intrinsic(&mut self, _value: Self::Value, _expected: bool) -> Self::Value {
        unimplemented!()
    }
}
