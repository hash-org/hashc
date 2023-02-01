//! Utilities for emitting declarations.

use hash_codegen::abi::{CallingConvention, FnAbi};
use inkwell::{
    types::{AnyTypeEnum, BasicTypeEnum},
    values::{FunctionValue, GlobalValue, UnnamedAddress},
    GlobalVisibility,
};

use super::abi::ExtendedFnAbiMethods;
use crate::context::CodeGenCtx;

impl<'b, 'm> CodeGenCtx<'b, 'm> {
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
        ty: AnyTypeEnum<'m>,
    ) -> FunctionValue<'m> {
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
        ty: AnyTypeEnum<'m>,
        calling_convention: CallingConvention,
        addr: UnnamedAddress,
        visibility: GlobalVisibility,
    ) -> FunctionValue<'m> {
        let func = if let Some(func) = self.module.get_function(name) {
            func
        } else {
            self.module.add_function(name, ty.into_function_type(), None)
        };

        // We need to apply the calling convention to the function
        func.set_call_conventions(calling_convention as u32);
        func.as_global_value().set_unnamed_address(addr);
        func.as_global_value().set_visibility(visibility);

        func
    }

    /// Declare a Hash function within the current [inkwell::module::Module].
    ///
    /// This will set some sane defaults when declaring the function, and apply
    /// all of the attributes onto the created [FunctionValue].
    pub(crate) fn declare_hash_fn(&self, name: &str, abi: &FnAbi) -> FunctionValue<'m> {
        let func = self.declare_fn(
            name,
            abi.llvm_ty(self),
            abi.calling_convention,
            UnnamedAddress::Global,
            GlobalVisibility::Default,
        );

        abi.apply_attributes_to_fn(self, func);
        func
    }

    /// Declare a global variable within the current [inkwell::module::Module]
    /// with the intent to define it.
    ///
    /// If the global variable name already exists, the function will return
    /// [`None`].
    pub(crate) fn declare_global(
        &self,
        name: &str,
        ty: BasicTypeEnum<'m>,
    ) -> Option<GlobalValue<'m>> {
        if self.module.get_global(name).is_some() {
            None
        } else {
            Some(self.module.add_global(ty, None, name))
        }
    }
}
