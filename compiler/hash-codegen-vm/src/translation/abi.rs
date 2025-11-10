//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{abi::ArgAbi, lower::place::PlaceRef, traits::abi::AbiBuilderMethods};

use crate::translation::VMBuilder;

impl<'b> AbiBuilderMethods<'b> for VMBuilder<'b> {
    fn get_param(&mut self, _index: usize) -> Self::Value {
        unimplemented!()
    }

    fn store_fn_call_arg(
        &mut self,
        _arg_abi: &ArgAbi,
        _value: Self::Value,
        _destination: PlaceRef<Self::Value>,
    ) {
        unimplemented!()
    }

    fn store_fn_arg(
        &mut self,
        _arg_abi: &ArgAbi,
        _index: &mut usize,
        _destination: PlaceRef<Self::Value>,
    ) {
        unimplemented!()
    }

    fn arg_ty(&mut self, _arg_abi: &ArgAbi) -> Self::Type {
        unimplemented!()
    }
}
