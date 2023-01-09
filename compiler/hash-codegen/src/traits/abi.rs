//! Defines a trait for representing ABI information about function, and
//! function arguments.

use hash_abi::{ArgAbi, FnAbi};
use hash_ir::ty::IrTyId;

use super::BackendTypes;
use crate::lower::place::PlaceRef;

pub trait AbiBuilderMethods<'b>: BackendTypes {
    /// Get a particular parameter from the ABI.
    fn get_param(&mut self, index: usize) -> Self::Value;

    /// Store an argument that is passed or returned from a
    /// function call.
    fn store_arg(
        &mut self,
        arg_abi: &ArgAbi,
        value: Self::Value,
        destination: PlaceRef<Self::Value>,
    );

    /// Specify that a particular function argument is to be
    /// stored in the specified [PlaceRef].
    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    );
}

pub trait FnAbiOf<'b> {
    fn fn_abi_of_instance(&self, ty: IrTyId) -> &'b FnAbi;
}
