//! Defines methods for resolving various information from the
//! code generation backend, and to set various "miscellaneous"
//! properties in the code generation backend, e.g. the
//! entry point of the program.

use hash_ir::ty;

use super::BackendTypes;

pub trait MiscBuilderMethods<'b>: BackendTypes {
    /// Get a function reference from an [ty::InstanceId].
    fn get_fn(&self, instance: ty::InstanceId) -> Self::Function;

    /// Get a function pointer from a [ty::InstanceId] whilst also
    /// applying all of the specified attributes that can appear
    /// on a function definition.
    fn get_fn_ptr(&self, instance: ty::InstanceId) -> Self::Value;

    /// Declare the program entry point
    fn declare_entry_point(&self, ty: Self::Type) -> Option<Self::Function>;
}
