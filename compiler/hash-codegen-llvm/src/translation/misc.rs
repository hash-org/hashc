//! Implements various miscellaneous methods for the LLVM backend.

use hash_codegen::{
    lower::abi::compute_fn_abi_from_instance,
    traits::{misc::MiscBuilderMethods, ty::TypeBuilderMethods},
};
use hash_ir::ty::InstanceId;
use inkwell::{
    values::{AnyValue, FunctionValue, UnnamedAddress},
    GlobalVisibility,
};

use super::abi::ExtendedFnAbiMethods;
use crate::context::CodeGenCtx;

impl<'b> CodeGenCtx<'b> {
    /// Generate code for a reference to a function or method item. The
    /// [Instance] specifies the function reference to generate, and any
    /// attributes that need to be applied to the function. If the function
    /// has already been generated, a reference will be returned from the
    /// cache.
    pub fn get_fn_or_create_ref(&self, instance: InstanceId) -> FunctionValue<'b> {
        // First check if we have already created the function reference...
        if let Some(fn_val) = self.instances.borrow().get(&instance) {
            return *fn_val;
        }

        let name = self.ir_ctx.instances().name_of(instance);

        // @@ErrorHandling: deal with error here...
        let fn_abi = compute_fn_abi_from_instance(self, instance).unwrap();

        // See if this item has already been declared in the module
        let func = if let Some(func) = self.module.get_function(name.into()) {
            // Create a function pointer with the new signature...
            let ptr = fn_abi.ptr_to_llvm_ty(self);

            // If the value type of the function does not match the
            // created pointer type, we have to create a pointer cast
            // between the two. @@Explain.
            if self.ty_of_value(func.into()).into_pointer_type() != ptr {
                let value = func.as_global_value().as_pointer_value().const_cast(ptr);
                value.as_any_value_enum().into_function_value()
            } else {
                // We don't need to cast here...
                func
            }
        } else {
            self.declare_hash_fn(name.into(), &fn_abi)
        };

        // We insert the function into the cache so that we can
        // reference it later on...
        self.instances.borrow_mut().insert(instance, func);

        func
    }
}

impl<'b> MiscBuilderMethods<'b> for CodeGenCtx<'b> {
    fn get_fn(&self, instance: InstanceId) -> Self::Function {
        self.get_fn_or_create_ref(instance)
    }

    fn get_fn_ptr(&self, instance: InstanceId) -> Self::Function {
        self.get_fn_or_create_ref(instance)
    }

    fn declare_entry_point(&self, fn_ty: Self::Type) -> Option<Self::Function> {
        let target = self.settings.codegen_settings().target_info.target();
        let entry_name = target.entry_name.as_ref();

        // If the symbol already exists, then it is an error
        if self.module.get_function(entry_name).is_some() {
            None
        } else {
            let abi = target.entry_abi;
            let visibility = if target.default_hidden_visibility {
                GlobalVisibility::Hidden
            } else {
                GlobalVisibility::Default
            };

            Some(self.declare_fn(entry_name, fn_ty, abi.into(), UnnamedAddress::Global, visibility))
        }
    }
}
