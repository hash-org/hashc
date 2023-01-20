//! Various utilities that are used within the IR lowering logic
//! to help with code generation.

use hash_layout::TyInfo;
use hash_target::alignment::Alignment;

use crate::{
    common::MemFlags,
    traits::{builder::BlockBuilderMethods, constants::BuildConstValueMethods},
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
    let size = builder.map_layout(ty.layout, |layout| layout.size.bytes());

    // we don't copy zsts.
    if size == 0 {
        return;
    }

    builder.memcpy(destination, source, builder.ctx().const_usize(size), flags)
}
