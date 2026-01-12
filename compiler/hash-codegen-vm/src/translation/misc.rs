use hash_codegen::{repr::ty, traits::misc::MiscBuilderMethods};
use hash_storage::store::statics::StoreId;

use crate::ctx::Ctx;

impl<'b> MiscBuilderMethods<'b> for Ctx<'b> {
    fn get_fn(&self, instance: ty::ReprTyId) -> Self::Function {
        instance.borrow().as_instance()
    }

    fn get_fn_ptr(&self, ty: ty::ReprTyId) -> Self::Value {
        self.get_fn_addr(ty)
    }

    fn get_fn_addr(&self, _ty: ty::ReprTyId) -> Self::Value {
        todo!()
    }

    fn declare_entry_point(&self, fn_ty: Self::Type) -> Option<Self::Function> {
        let instance = fn_ty.borrow().as_instance();

        Some(instance)
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
