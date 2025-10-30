//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{repr::TyInfo, traits::layout::LayoutMethods};

use crate::{ctx::Ctx, translation::VMBuilder};

impl<'b> LayoutMethods<'b> for Ctx<'b> {
    fn backend_field_index(&self, _info: TyInfo, _index: usize) -> u64 {
        todo!()
    }

    fn is_backend_immediate(&self, _info: TyInfo) -> bool {
        todo!()
    }

    fn is_backend_scalar_pair(&self, _info: TyInfo) -> bool {
        todo!()
    }
}

impl<'b> LayoutMethods<'b> for VMBuilder<'b> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.ctx.backend_field_index(info, index)
    }

    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        self.ctx.is_backend_immediate(info)
    }

    fn is_backend_scalar_pair(&self, info: TyInfo) -> bool {
        self.ctx.is_backend_scalar_pair(info)
    }
}
