//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{abi::ArgAbi, lower::place::PlaceRef, traits::abi::AbiBuilderMethods};
use hash_ir::ir::Const;

use crate::translation::VMBuilder;

impl<'b> AbiBuilderMethods<'b> for VMBuilder<'_, 'b> {
    fn get_param(&mut self, _index: usize) -> Self::Value {
        unimplemented!()
    }

    fn store_fn_call_arg(
        &mut self,
        arg_abi: &ArgAbi,
        value: Self::Value,
        destination: PlaceRef<Self::Value>,
    ) {
        arg_abi.store(self, value, destination)
    }

    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    ) {
        arg_abi.store_fn_arg(self, index, destination)
    }

    fn arg_ty(&mut self, arg_abi: &ArgAbi) -> Self::Type {
        arg_abi.info.ty
    }
}

pub trait ExtendedArgAbiMethods<'b, 'm> {
    fn store(&self, builder: &mut VMBuilder<'_, 'm>, value: Const, destination: PlaceRef<Const>);

    fn store_fn_arg(
        &self,
        builder: &mut VMBuilder<'b, 'm>,
        index: &mut usize,
        destination: PlaceRef<Const>,
    );
}

impl<'b, 'm> ExtendedArgAbiMethods<'b, 'm> for ArgAbi {
    fn store(
        &self,
        _builder: &mut VMBuilder<'_, 'm>,
        _value: Const,
        _destination: PlaceRef<Const>,
    ) {
        // @@TODO: do not emit anything for now.
    }

    fn store_fn_arg(
        &self,
        _builder: &mut VMBuilder<'b, 'm>,
        _index: &mut usize,
        _destination: PlaceRef<Const>,
    ) {
        // @@TODO: do not emit anything for now.
    }
}
