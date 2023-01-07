//! Defines a trait for representing ABI information about function, and
//! function arguments.

use hash_abi::ArgAbi;

use super::BackendTypes;
use crate::lower::place::PlaceRef;

pub trait AbiBuilderMethods<'b>: BackendTypes {
    /// Get a particular parameter from the ABI.
    fn get_param(&mut self, index: usize) -> Self::Value;

    /// Specify that a particular function argument is to be
    /// stored in the specified [PlaceRef].
    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    );
}
