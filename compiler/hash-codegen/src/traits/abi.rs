//! Defines a trait for representing ABI information about function, and
//! function arguments.

use super::BackendTypes;

pub trait AbiBuilderMethods<'b>: BackendTypes {
    /// Get a particular parameter from the ABI.
    fn get_param(&mut self, index: usize) -> Self::Value;
}
