//! Implementation for all of the specified methods of
//! [hash_codegen::traits::builder::BlockBuilderMethods] using the Inkwell
//! wrapper around LLVM.

use hash_codegen::{
    common::MemFlags,
    lower::{operands::OperandRef, place::PlaceRef},
    traits::builder::BlockBuilderMethods,
};
use hash_target::{abi::ValidScalarRange, alignment::Alignment, size::Size};

use super::Builder;

impl<'b> BlockBuilderMethods<'b> for Builder<'b> {
    fn build(ctx: &'b Self::CodegenCtx, block: Self::BasicBlock) -> Self {
        todo!()
    }

    fn append_block(
        ctx: &'b Self::CodegenCtx,
        func: Self::Function,
        name: &str,
    ) -> Self::BasicBlock {
        todo!()
    }

    fn append_sibling_block(&mut self, name: &str) -> Self::BasicBlock {
        todo!()
    }

    fn ctx(&self) -> &Self::CodegenCtx {
        todo!()
    }

    fn basic_block(&self) -> Self::BasicBlock {
        todo!()
    }

    fn switch_to_block(&mut self, block: Self::BasicBlock) {
        todo!()
    }

    fn return_value(&mut self, value: Self::Value) {
        todo!()
    }

    fn return_void(&mut self) {
        todo!()
    }

    fn branch(&mut self, destination: Self::BasicBlock) {
        todo!()
    }

    fn conditional_branch(
        &mut self,
        condition: Self::Value,
        true_block: Self::BasicBlock,
        false_block: Self::BasicBlock,
    ) {
        todo!()
    }

    fn switch(
        &mut self,
        condition: Self::Value,
        cases: impl ExactSizeIterator<Item = (u128, Self::BasicBlock)>,
        otherwise_block: Self::BasicBlock,
    ) {
        todo!()
    }

    fn unreachable(&mut self) {
        todo!()
    }

    fn checked_call(
        &mut self,
        ty: Self::Type,
        args: &[Self::Value],
        then_block: Self::BasicBlock,
        catch_block: Self::BasicBlock,
    ) -> Self::Value {
        todo!()
    }

    fn call(
        &mut self,
        ty: Self::Type,
        fn_abi: Option<&hash_codegen::abi::FnAbi>,
        fn_ptr: Self::Value,
        args: &[Self::Value],
    ) -> Self::Value {
        todo!()
    }

    fn add(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fadd_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn sub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fsub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fsub_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn mul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fmul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fmul_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn udiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn exactudiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn sdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn exactsdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fdiv_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn urem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn srem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn frem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn frem_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fpow(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn shl(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn lshr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn ashr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_sadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_uadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_ssub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_usub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_smul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_umul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn and(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn or(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn xor(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn not(&mut self, v: Self::Value) -> Self::Value {
        todo!()
    }

    fn neg(&mut self, v: Self::Value) -> Self::Value {
        todo!()
    }

    fn fneg(&mut self, v: Self::Value) -> Self::Value {
        todo!()
    }

    fn checked_bin_op(
        &mut self,
        op: hash_codegen::common::CheckedOp,
        lhs: Self::Value,
        rhs: Self::Value,
    ) -> (Self::Value, Self::Value) {
        todo!()
    }

    fn icmp(
        &mut self,
        op: hash_codegen::common::IntComparisonKind,
        lhs: Self::Value,
        rhs: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn fcmp(
        &mut self,
        op: hash_codegen::common::RealComparisonKind,
        lhs: Self::Value,
        rhs: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn sign_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn zero_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_ui_sat(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_si_sat(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_ui(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_si(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn ui_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn si_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn ptr_to_int(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn int_to_ptr(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn bit_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn int_cast(&mut self, val: Self::Value, dest_ty: Self::Type, is_signed: bool) -> Self::Value {
        todo!()
    }

    fn pointer_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn bool_from_immediate(&mut self, v: Self::Value) -> Self::Value {
        todo!()
    }

    fn to_immediate_scalar(
        &mut self,
        v: Self::Value,
        scalar_kind: hash_target::abi::Scalar,
    ) -> Self::Value {
        todo!()
    }

    fn alloca(&mut self, ty: Self::Type, alignment: Alignment) -> Self::Value {
        todo!()
    }

    fn byte_array_alloca(&mut self, len: Self::Value, alignment: Alignment) -> Self::Value {
        todo!()
    }

    fn write_operand_repeatedly(
        &mut self,
        operand: OperandRef<Self::Value>,
        count: usize,
        destination: PlaceRef<Self::Value>,
    ) {
        todo!()
    }

    fn load(&mut self, ty: Self::Type, ptr: Self::Value, alignment: Alignment) -> Self::Value {
        todo!()
    }

    fn volatile_load(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        alignment: Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn atomic_load(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        alignment: Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn load_operand(&mut self, place: PlaceRef<Self::Value>) -> OperandRef<Self::Value> {
        todo!()
    }

    fn store(&mut self, value: Self::Value, ptr: Self::Value, alignment: Alignment) -> Self::Value {
        todo!()
    }

    fn store_with_flags(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        flags: hash_codegen::common::MemFlags,
    ) -> Self::Value {
        todo!()
    }

    fn atomic_store(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        ordering: std::sync::atomic::Ordering,
    ) -> Self::Value {
        todo!()
    }

    fn get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value {
        todo!()
    }

    fn bounded_get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value {
        todo!()
    }

    fn structural_get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        index: u64,
    ) -> Self::Value {
        todo!()
    }

    fn memcpy(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    ) {
        todo!()
    }

    fn memmove(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    ) {
        todo!()
    }

    fn memset(
        &mut self,
        ptr: Self::Value,
        fill: Self::Value,
        size: Self::Value,
        align: Alignment,
        flags: MemFlags,
    ) {
        todo!()
    }

    fn select(
        &mut self,
        condition: Self::Value,
        then: Self::Value,
        otherwise: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn lifetime_start(&mut self, ptr: Self::Value, size: Size) {
        todo!()
    }

    fn lifetime_end(&mut self, ptr: Self::Value, size: Size) {
        todo!()
    }

    fn add_range_metadata_to(&mut self, value: Self::Value, range: ValidScalarRange) {
        todo!()
    }
}
