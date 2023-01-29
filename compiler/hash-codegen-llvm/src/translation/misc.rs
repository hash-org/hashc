//! Implements various miscellaneous methods for the LLVM backend.

use hash_codegen::traits::misc::MiscBuilderMethods;
use hash_ir::ty::{Instance, InstanceId};
use inkwell::values::FunctionValue;

use crate::context::CodeGenCtx;

impl<'b> CodeGenCtx<'b> {
    /// Generate code for a reference to a function or method item. The
    /// [Instance] specifies the function reference to generate, and any
    /// attributes that need to be applied to the function. If the function
    /// has already been generated, a reference will be returned from the
    /// cache.
    pub fn get_fn_or_create_ref(&self, instance: InstanceId) -> FunctionValue<'b> {
        todo!()
    }
}

impl<'b> MiscBuilderMethods<'b> for CodeGenCtx<'b> {
    fn get_fn(&self, instance: InstanceId) -> Self::Function {
        self.get_fn_or_create_ref(instance)
    }

    fn get_fn_ptr(&self, instance: InstanceId) -> Self::Value {
        self.get_fn_or_create_ref(instance).into()
    }

    fn declare_entry_point(&self, ty: Self::Type) -> Option<Self::Function> {
        todo!()
    }
}
