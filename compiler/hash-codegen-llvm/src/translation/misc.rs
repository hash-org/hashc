//! Implements various miscellaneous methods for the LLVM backend.

use hash_codegen::{
    abi::{CallingConvention, FnAbi},
    symbols::mangle::compute_symbol_name,
    traits::{misc::MiscBuilderMethods, ty::TypeBuilderMethods, HasCtxMethods},
};
use hash_ir::ty::InstanceId;
use hash_source::identifier::IDENTS;
use hash_utils::store::Store;
use inkwell::{
    module::Linkage,
    values::{AnyValue, FunctionValue, UnnamedAddress},
    GlobalVisibility,
};

use super::abi::ExtendedFnAbiMethods;
use crate::ctx::CodeGenCtx;

impl<'b, 'm> CodeGenCtx<'b, 'm> {
    /// Generate code for a reference to a function or method item. The
    /// [Instance] specifies the function reference to generate, and any
    /// attributes that need to be applied to the function. If the function
    /// has already been generated, a reference will be returned from the
    /// cache.
    pub fn get_fn_or_create_ref(&self, instance: InstanceId) -> FunctionValue<'m> {
        // First check if we have already created the function reference...
        if let Some(fn_val) = self.instances.borrow().get(&instance) {
            return *fn_val;
        }

        let name = compute_symbol_name(self.ir_ctx, instance);
        let abis = self.cg_ctx().abis();
        let fn_abi = abis.create_fn_abi(self, instance);

        // See if this item has already been declared in the module
        let func = if let Some(func) = self.module.get_function(name.as_str()) {
            // Create a function pointer with the new signature...
            let ptr = abis.map_fast(fn_abi, |abi| abi.ptr_to_llvm_ty(self));

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
            abis.map_fast(fn_abi, |abi| self.declare_hash_fn(name.as_str(), abi))
        };

        // We insert the function into the cache so that we can
        // reference it later on...
        self.instances.borrow_mut().insert(instance, func);

        func
    }
}

impl<'b, 'm> MiscBuilderMethods<'b> for CodeGenCtx<'b, 'm> {
    fn get_fn(&self, instance: InstanceId) -> Self::Function {
        self.get_fn_or_create_ref(instance)
    }

    fn get_fn_ptr(&self, instance: InstanceId) -> Self::Function {
        self.get_fn_or_create_ref(instance)
    }

    fn declare_entry_point(&self, fn_ty: Self::Type) -> Option<Self::Function> {
        let target = self.target();
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

            let convention = CallingConvention::make_from_abi_and_target(abi, target);
            let func =
                self.declare_fn(entry_name, fn_ty, convention, UnnamedAddress::Global, visibility);
            func.set_linkage(Linkage::External);

            Some(func)
        }
    }

    /// This function is used to pre-define the function before the LLVM
    /// IR is emitted for it. This function is only a wrapper for
    /// `declare_hash_fn`, however, in the future, it will accept custom
    /// linkage and visibility types in order to adjust the definition from
    /// a default one.
    fn predefine_fn(&self, instance: InstanceId, symbol_name: &str, fn_abi: &FnAbi) {
        let decl = self.declare_hash_fn(symbol_name, fn_abi);

        // If the instance has the "foreign" attribute, then we need to
        // specify that the linkage is external.
        self.ir_ctx.map_instance(instance, |instance| {
            if instance.attributes.contains(IDENTS.foreign) {
                decl.set_linkage(Linkage::External);
            }
        });

        // We insert the function into the cache so that we can
        // reference it later on...
        self.instances.borrow_mut().insert(instance, decl);
    }
}
