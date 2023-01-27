//! Contains utility methods for emitting LLVM metadata about
//! values, functions, and types.

use hash_codegen::traits::{
    builder::BlockBuilderMethods, constants::ConstValueBuilderMethods, ty::BuildTypeMethods,
    BackendTypes,
};
use hash_target::{alignment::Alignment, size::Size};
use inkwell as llvm;
use llvm::{
    intrinsics::Intrinsic,
    values::{AnyValueEnum, BasicMetadataValueEnum, BasicValueEnum},
};

use super::Builder;
use crate::misc::MetadataType;

impl<'b> Builder<'b> {
    /// Emit a `no-undef` metadata attribute on a specific value.
    pub fn set_no_undef(&mut self, value: AnyValueEnum<'b>) {
        let value = value.into_instruction_value();

        let metadata = self.ctx.ll_ctx.metadata_node(&[]);
        value.set_metadata(metadata, MetadataType::NoUndef as u32);
    }

    /// Emit a `nonnull` metadata attribute on a specific value.
    pub fn set_non_null(&mut self, value: AnyValueEnum<'b>) {
        let value = value.into_instruction_value();

        let metadata = self.ctx.ll_ctx.metadata_node(&[]);
        value.set_metadata(metadata, MetadataType::NonNull as u32);
    }

    /// Specify the alignment for a particular value.
    pub fn set_alignment(&mut self, value: AnyValueEnum<'b>, alignment: Alignment) {
        let value = value.into_instruction_value();

        let alignment_metadata: BasicMetadataValueEnum =
            self.ctx.const_u64(alignment.bytes()).try_into().unwrap();

        let metadata = self.ctx.ll_ctx.metadata_node(&[alignment_metadata]);

        value.set_metadata(metadata, MetadataType::Align as u32);
    }

    /// Emit lifetime marker information to LLVM via a `llvm.lifetime.start`
    /// or `llvm.lifetime.end` intrinsic.
    pub fn emit_lifetime_marker(&mut self, intrinsic: &str, ptr: AnyValueEnum<'b>, size: Size) {
        let size = size.bytes();

        // We don't do anything if this is a unit.
        if size == 0 {
            return;
        }

        let size = self.ctx.const_u64(size);
        let ptr = self.pointer_cast(ptr, self.ctx.type_i8p());

        self.call_intrinsic(intrinsic, &[size, ptr]);
    }
}
