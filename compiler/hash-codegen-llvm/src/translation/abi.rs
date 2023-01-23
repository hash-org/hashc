//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{abi::ArgAbi, lower::place::PlaceRef, traits::abi::AbiBuilderMethods};

use super::Builder;

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
