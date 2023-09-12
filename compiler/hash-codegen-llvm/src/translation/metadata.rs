//! Contains utility methods for emitting LLVM metadata about
//! values, functions, and types.

use hash_codegen::{
    target::{alignment::Alignment, size::Size},
    traits::constants::ConstValueBuilderMethods,
};
use inkwell as llvm;
use llvm::values::{AnyValueEnum, BasicMetadataValueEnum, InstructionValue};

use super::LLVMBuilder;
use crate::misc::MetadataTypeKind;

impl<'m> LLVMBuilder<'_, '_, 'm> {
    /// Emit a `no-undef` metadata attribute on a specific value.
    pub fn set_no_undef(&mut self, value: InstructionValue<'m>) {
        let metadata = self.ctx.ll_ctx.metadata_node(&[]);
        value.set_metadata(metadata, MetadataTypeKind::NoUndef as u32).unwrap();
    }

    /// Emit a `nonnull` metadata attribute on a specific value.
    pub fn set_non_null(&mut self, value: InstructionValue<'m>) {
        let metadata = self.ctx.ll_ctx.metadata_node(&[]);
        value.set_metadata(metadata, MetadataTypeKind::NonNull as u32).unwrap();
    }

    /// Specify the alignment for a particular value.
    pub fn set_alignment(&mut self, value: InstructionValue<'m>, alignment: Alignment) {
        let alignment_metadata: BasicMetadataValueEnum =
            self.ctx.const_u64(alignment.bytes()).try_into().unwrap();

        let metadata = self.ctx.ll_ctx.metadata_node(&[alignment_metadata]);

        value.set_metadata(metadata, MetadataTypeKind::Align as u32).unwrap();
    }

    /// Emit lifetime marker information to LLVM via a `llvm.lifetime.start`
    /// or `llvm.lifetime.end` intrinsic.
    pub fn emit_lifetime_marker(&mut self, intrinsic: &str, ptr: AnyValueEnum<'m>, size: Size) {
        let size = size.bytes();

        // We don't do anything if this is a unit.
        if size == 0 {
            return;
        }

        self.call_intrinsic(intrinsic, &[self.ctx.const_u64(size), ptr]);
    }
}
