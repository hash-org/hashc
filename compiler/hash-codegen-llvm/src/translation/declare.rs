//! Utilities for emitting declarations.

use hash_codegen::abi::CallingConvention;
use inkwell::{
    types::AnyTypeEnum,
    values::{AnyValueEnum, UnnamedAddress},
    GlobalVisibility,
};

use super::Builder;

impl<'b> Builder<'b> {
    /// Standard function to declare a C-like function. This should only be used
    /// for declaring FFI functions or various LLVM intrinsics.
    ///
    /// N.B. An [UnnamedAddress] specifies the significance of the global
    /// value's address. Functions are treated as global values in LLVM IR.
    /// The options are specified within the [documentation](https://llvm.org/doxygen/group__LLVMCCoreTypes.html#gaa12598f8d5c36303fae1e1192cbb1b33).
    ///
    /// Also, from the language reference:
    /// ```text
    /// Global variables can be marked with unnamed_addr which indicates that the
    /// address is not significant, only the content. Constants marked like this can
    /// be merged with other constants if they have the same initializer. Note that a
    /// constant with significant address can be merged with a unnamed_addr constant,
    /// the result being a constant whose address is significant.
    /// ```
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#global-variables>
    pub(crate) fn declare_c_fn(
        &self,
        name: &str,
        addr: UnnamedAddress,
        ty: AnyTypeEnum<'b>,
    ) -> AnyValueEnum<'b> {
        self.declare_fn(
            name,
            ty,
            CallingConvention::C,
            addr,
            // @@Todo: maybe make this configurable through the target?
            GlobalVisibility::Default,
        )
    }

    /// Declare a function within the current [inkwell::module::Module]. If the
    /// function name already exists, the existing function is updated with the
    /// specified [CallingConvention], [UnnamedAddress], and [GlobalVisibility].
    pub(crate) fn declare_fn(
        &self,
        name: &str,
        ty: AnyTypeEnum<'b>,
        calling_convention: CallingConvention,
        addr: UnnamedAddress,
        visibility: GlobalVisibility,
    ) -> AnyValueEnum<'b> {
        let func = if let Some(func) = self.module.get_function(name) {
            func
        } else {
            self.module.add_function(name, ty.into_function_type(), None)
        };

        // We need to apply the calling convention to the function
        func.set_call_conventions(calling_convention as u32);
        func.as_global_value().set_unnamed_address(addr);
        func.as_global_value().set_visibility(visibility);

        func.into()
    }
}
