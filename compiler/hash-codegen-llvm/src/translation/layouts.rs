//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{layout::TyInfo, traits::layout::LayoutMethods};
use hash_target::data_layout::{HasDataLayout, TargetDataLayout};

use super::{context::CodeGenCtx, Builder};

impl<'b> LayoutMethods<'b> for CodeGenCtx<'b> {
    fn layout_of_id(&self, ty: hash_ir::ty::IrTyId) -> hash_codegen::layout::TyInfo {
        todo!()
    }

    fn layout_of(&self, ty: hash_ir::ty::IrTy) -> hash_codegen::layout::TyInfo {
        todo!()
    }

    fn backend_field_index(&self, info: hash_codegen::layout::TyInfo, index: usize) -> u64 {
        todo!()
    }

    fn is_backend_immediate(&self, ty: hash_codegen::layout::TyInfo) -> bool {
        todo!()
    }

    fn scalar_pair_element_backend_type(
        &self,
        info: hash_codegen::layout::TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        todo!()
    }
}

impl HasDataLayout for CodeGenCtx<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        todo!()
    }
}

impl<'b> LayoutMethods<'b> for Builder<'b> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.ctx.backend_field_index(info, index)
    }

    fn is_backend_immediate(&self, ty: TyInfo) -> bool {
        self.ctx.is_backend_immediate(ty)
    }

    fn scalar_pair_element_backend_type(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        self.ctx.scalar_pair_element_backend_type(info, index, immediate)
    }
}

impl HasDataLayout for Builder<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.ctx.data_layout()
    }
}
