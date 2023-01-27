//! Implements various miscellaneous methods for the LLVM backend.

use hash_codegen::traits::misc::MiscBuilderMethods;

use crate::context::CodeGenCtx;

impl<'b> MiscBuilderMethods<'b> for CodeGenCtx<'b> {
    fn get_fn(&self, instance: hash_ir::ty::Instance) -> Self::Function {
        todo!()
    }

    fn get_fn_ptr(&self, instance: hash_ir::ty::Instance) -> Self::Value {
        todo!()
    }

    fn declare_entry_point(&self, ty: Self::Type) -> Option<Self::Function> {
        todo!()
    }
}
