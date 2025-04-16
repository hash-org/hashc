//! Utility helper functions to lower TIR types into [ReprTy] format. This
//! only wraps the logic that is present in TIR lowering.

use hash_ast::ast::AstNodeId;
use hash_attrs::builtin::attrs;
use hash_ir::{HasIrCtx, intrinsics::Intrinsic, lang_items::LangItem, ty::InstanceHelpers};
use hash_repr::ty::{Instance, ReprTy, ReprTyId, ReprTyListId};
use hash_storage::store::statics::{SingleStoreValue, StoreId};
use hash_tir::{
    intrinsics::{definitions::Intrinsic as TirIntrinsic, make::IsIntrinsic},
    tir::{DataTy, FnDefId, FnTy, NodesId, TyId},
};
use hash_tir_utils::lower::{ShouldCache, TyLower};

use crate::ctx::BuilderCtx;

impl BuilderCtx<'_> {
    pub(crate) fn repr_ty_from_tir_ty(&self, id: TyId) -> ReprTyId {
        let lower = TyLower::new(self);
        lower.repr_ty_from_tir_ty(id)
    }

    pub(crate) fn repr_ty_from_tir_data_ty(&self, data_ty: DataTy) -> ReprTyId {
        let lower = TyLower::new(self);
        lower.repr_ty_from_tir_data_ty(data_ty)
    }

    pub(crate) fn repr_ty_from_tir_fn_def(&self, fn_def: FnDefId) -> ReprTyId {
        let lower = TyLower::new(self);
        lower.repr_ty_from_tir_fn_def(fn_def)
    }

    pub(crate) fn repr_ty_from_tir_intrinsic(
        &mut self,
        intrinsic: TirIntrinsic,
        originating_node: AstNodeId,
    ) -> ReprTyId {
        let lower = TyLower::new(self);

        lower.with_cache(intrinsic, || {
            let instance = self.create_instance_from_intrinsic(intrinsic, originating_node);

            let is_lang = instance.has_attr(attrs::LANG);
            let name = instance.name();

            // Check if the instance has the `lang` attribute, specifying that it is
            // the lang-item attribute.
            let instance = Instance::create(instance);
            let ty = ReprTy::create(ReprTy::FnDef { instance });

            if is_lang {
                let item = LangItem::from_str_name(name.into());
                self.ir_ctx().lang_items_mut().set(item, instance, ty);
            }

            // The function is an intrinsic function
            let item = Intrinsic::from_str_name(name.into()).expect("unknown intrinsic function");
            self.ir_ctx().intrinsics_mut().set(item, instance, ty);

            (ty, ShouldCache::Yes)
        })
    }

    /// Create a [Instance] from a [Intrinsic].
    ///
    /// Only some of the [Intrinsic]s have equivalents in the IR [Intrinsic]
    /// enum.
    fn create_instance_from_intrinsic(
        &self,
        intrinsic: TirIntrinsic,
        originating_node: AstNodeId,
    ) -> Instance {
        let FnTy { params, return_ty, .. } = intrinsic.ty();

        let params = ReprTyListId::seq(
            params.elements().borrow().iter().map(|param| self.repr_ty_from_tir_ty(param.ty)),
        );
        let ret_ty = self.repr_ty_from_tir_ty(return_ty);

        let ident = intrinsic.name();
        let mut instance = Instance::new(ident, None, params, ret_ty, originating_node);

        if Intrinsic::from_str_name(ident.into()).is_some() {
            instance.is_intrinsic = true;
        }

        instance
    }
}
