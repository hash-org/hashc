//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{
    abi::{ArgAbi, FnAbi},
    lower::place::PlaceRef,
    traits::abi::AbiBuilderMethods,
};
use inkwell::{
    types::{AnyTypeEnum, BasicTypeEnum},
    values::{CallSiteValue, FunctionValue},
};

use super::{context::CodeGenCtx, Builder};

impl<'b> AbiBuilderMethods<'b> for Builder<'b> {
    fn get_param(&mut self, index: usize) -> Self::Value {
        todo!()
    }

    fn store_arg(
        &mut self,
        arg_abi: &ArgAbi,
        value: Self::Value,
        destination: PlaceRef<Self::Value>,
    ) {
        todo!()
    }

    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    ) {
        todo!()
    }
}

pub trait ExtendedFnAbiMethods<'b> {
    /// Produce an LLVM type for the given [FnAbi].
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b>;

    /// Apply the derived ABI attributes to the given [FunctionValue].
    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'b>, func: FunctionValue<'b>);

    /// Apply the derived ABI attributes to the given [CallSiteValue].
    fn apply_attributes_call_site(&self, builder: &mut Builder<'b>, call_site: CallSiteValue<'b>);
}

impl<'b> ExtendedFnAbiMethods<'b> for FnAbi {
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b> {
        todo!()
    }

    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'b>, func: FunctionValue<'b>) {
        todo!()
    }

    fn apply_attributes_call_site(&self, builder: &mut Builder<'b>, call_site: CallSiteValue<'b>) {
        todo!()
    }
}
