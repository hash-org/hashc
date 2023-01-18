//! Various utilities that are used within the IR lowering logic
//! to help with code generation.

use hash_abi::FnAbi;
use hash_ir::ty::{IrTy, IrTyId};
use hash_layout::TyInfo;
use hash_target::alignment::Alignment;

use super::FnBuilder;
use crate::{
    common::MemFlags,
    traits::{builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods},
};

/// Emit a `memcpy` instruction for a particular value with the provided
/// alignment, [MemFlags] and [TyInfo].
///
/// N.B. If the type is a ZST, then this will not emit a `memcpy`
/// instruction.
pub fn mem_copy_ty<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    destination: (Builder::Value, Alignment),
    source: (Builder::Value, Alignment),
    ty: TyInfo,
    flags: MemFlags,
) {
    let size = builder.layout_info(ty.layout).size.bytes();

    // we don't copy zsts.
    if size == 0 {
        return;
    }

    builder.memcpy(destination, source, builder.ctx().const_usize(size), flags)
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Compute an [FnAbi] from a provided [IrTyId]. If the ABI
    /// has already been computed for the particular instance, then
    /// the cached version of the ABI is returned.
    ///
    /// N.B. the passed "ty" must be a function type.
    pub fn compute_fn_abi_from_ty(&mut self, ty: IrTyId) -> &FnAbi {
        // @@Todo: add caching for the ABI computation...

        self.ctx.ir_ctx().map_ty(ty, |ty| {
            let IrTy::Fn { .. } = ty else {
                unreachable!("expected a function type")
            };

            todo!()
        })
    }
}
