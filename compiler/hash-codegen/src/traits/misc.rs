//! Defines methods for resolving various information from the
//! code generation backend, and to set various "miscellaneous"
//! properties in the code generation backend, e.g. the
//! entry point of the program.

use hash_abi::FnAbi;
use hash_ir::ty::{self, InstanceId};

use super::BackendTypes;

pub trait MiscBuilderMethods<'b>: BackendTypes {
    /// Get a function reference from an [ty::ReprTyId].
    /// 
    /// ##Note: It is assumed that the passed type is a [ty::ReprTy::FnDef].
    fn get_fn(&self, ty: ty::ReprTyId) -> Self::Function;

    /// Get a function pointer from a [ty::ReprTyId] whilst also
    /// applying all of the specified attributes that can appear
    /// on a function definition.
    /// 
    /// ##Note: It is assumed that the passed type is a [ty::ReprTy::FnDef].
    fn get_fn_ptr(&self, ty: ty::ReprTyId) -> Self::Value;

    /// Get a function pointer from a [ty::ReprTyId] whilst also
    /// applying all of the specified attributes that can appear
    /// on a function definition.
    /// 
    /// ##Note: It is assumed that the passed type is a [ty::ReprTy::FnDef].
    fn get_fn_addr(&self, ty: ty::ReprTyId) -> Self::Value;

    /// Declare the program entry point.
    fn declare_entry_point(&self, ty: Self::Type) -> Option<Self::Function>;

    /// Pre-define a function based on the [InstanceId].
    fn predefine_fn(&self, instance: InstanceId, symbol_name: &str, fn_abi: &FnAbi);
}
