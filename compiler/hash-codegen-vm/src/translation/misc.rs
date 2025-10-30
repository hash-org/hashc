use hash_codegen::traits::misc::MiscBuilderMethods;

use crate::ctx::Ctx;

impl<'b> MiscBuilderMethods<'b> for Ctx<'b> {
    fn get_fn(&self, _instance: hash_ir::ty::InstanceId) -> Self::Function {
        todo!()
    }

    fn get_fn_ptr(&self, _instance: hash_ir::ty::InstanceId) -> Self::Value {
        todo!()
    }

    fn get_fn_addr(&self, _instance: hash_ir::ty::InstanceId) -> Self::Value {
        todo!()
    }

    fn declare_entry_point(&self, _fn_ty: Self::Type) -> Option<Self::Function> {
        todo!()
    }

    fn predefine_fn(
        &self,
        _instance: hash_ir::ty::InstanceId,
        _symbol_name: &str,
        _fn_abi: &hash_codegen::abi::FnAbi,
    ) {
        todo!()
    }
}
