use hash_codegen::traits::builder::BlockBuilderMethods;

use crate::translation::VMBuilder;

impl<'a, 'b> BlockBuilderMethods<'a, 'b> for VMBuilder<'b> {
    fn ctx(&self) -> &Self::CodegenCtx {
        todo!()
    }

    fn build(_ctx: &'a Self::CodegenCtx, _block: Self::BasicBlock) -> Self {
        todo!()
    }

    fn append_block(
        _ctx: &'a Self::CodegenCtx,
        _func: Self::Function,
        _name: &str,
    ) -> Self::BasicBlock {
        todo!()
    }

    fn append_sibling_block(&mut self, _name: &str) -> Self::BasicBlock {
        todo!()
    }

    fn basic_block(&self) -> Self::BasicBlock {
        todo!()
    }

    fn switch_to_block(&mut self, _block: Self::BasicBlock) {
        todo!()
    }

    fn return_value(&mut self, _value: Self::Value) {
        todo!()
    }

    fn return_void(&mut self) {
        todo!()
    }

    fn branch(&mut self, _destination: Self::BasicBlock) {
        todo!()
    }

    fn conditional_branch(
        &mut self,
        _condition: Self::Value,
        _true_block: Self::BasicBlock,
        _false_block: Self::BasicBlock,
    ) {
        todo!()
    }

    fn switch(
        &mut self,
        _condition: Self::Value,
        _cases: impl ExactSizeIterator<Item = (u128, Self::BasicBlock)>,
        _otherwise_block: Self::BasicBlock,
    ) {
        todo!()
    }

    fn unreachable(&mut self) {
        todo!()
    }

    fn call(
        &mut self,
        _fn_ty: Self::Type,
        _fn_ptr: Self::Value,
        _args: &[Self::Value],
        _fn_abi: Option<hash_codegen::abi::FnAbiId>,
    ) -> Self::Value {
        todo!()
    }

    fn add(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fadd(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fadd_fast(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn sub(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fsub(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fsub_fast(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn mul(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fmul(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fmul_fast(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn udiv(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn exactudiv(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn sdiv(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn exactsdiv(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fdiv(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fdiv_fast(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn urem(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn srem(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn frem(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn frem_fast(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn fpow(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn shl(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn lshr(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn ashr(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_sadd(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_uadd(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_ssub(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_usub(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_smul(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn unchecked_umul(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn and(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn or(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn xor(&mut self, _lhs: Self::Value, _rhs: Self::Value) -> Self::Value {
        todo!()
    }

    fn not(&mut self, _v: Self::Value) -> Self::Value {
        todo!()
    }

    fn neg(&mut self, _v: Self::Value) -> Self::Value {
        todo!()
    }

    fn fneg(&mut self, _v: Self::Value) -> Self::Value {
        todo!()
    }

    fn checked_bin_op(
        &mut self,
        _op: hash_codegen::common::CheckedOp,
        _ty: hash_ir::ty::ReprTyId,
        _lhs: Self::Value,
        _rhs: Self::Value,
    ) -> (Self::Value, Self::Value) {
        todo!()
    }

    fn icmp(
        &mut self,
        _op: hash_codegen::common::IntComparisonKind,
        _lhs: Self::Value,
        _rhs: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn fcmp(
        &mut self,
        _op: hash_codegen::common::RealComparisonKind,
        _lhs: Self::Value,
        _rhs: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn truncate(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn sign_extend(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn zero_extend(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_int_sat(
        &mut self,
        _val: Self::Value,
        _dest_ty: Self::Type,
        _signed: bool,
    ) -> Self::Value {
        todo!()
    }

    fn fp_to_ui(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_to_si(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn ui_to_fp(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn si_to_fp(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_truncate(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn fp_extend(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn ptr_to_int(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn int_to_ptr(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn bit_cast(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn int_cast(
        &mut self,
        _val: Self::Value,
        _dest_ty: Self::Type,
        _is_signed: bool,
    ) -> Self::Value {
        todo!()
    }

    fn pointer_cast(&mut self, _val: Self::Value, _dest_ty: Self::Type) -> Self::Value {
        todo!()
    }

    fn value_from_immediate(&mut self, _v: Self::Value) -> Self::Value {
        todo!()
    }

    fn to_immediate_scalar(
        &mut self,
        _v: Self::Value,
        _scalar_kind: hash_codegen::target::abi::Scalar,
    ) -> Self::Value {
        todo!()
    }

    fn alloca(
        &mut self,
        _ty: Self::Type,
        _alignment: hash_codegen::target::alignment::Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn byte_array_alloca(
        &mut self,
        _len: Self::Value,
        _alignment: hash_codegen::target::alignment::Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn write_operand_repeatedly(
        &mut self,
        _operand: hash_codegen::lower::operands::OperandRef<Self::Value>,
        _count: usize,
        _destination: hash_codegen::lower::place::PlaceRef<Self::Value>,
    ) {
        todo!()
    }

    fn load(
        &mut self,
        _ty: Self::Type,
        _ptr: Self::Value,
        _alignment: hash_codegen::target::alignment::Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn volatile_load(&mut self, _ty: Self::Type, _ptr: Self::Value) -> Self::Value {
        todo!()
    }

    fn atomic_load(
        &mut self,
        _ty: Self::Type,
        _ptr: Self::Value,
        _ordering: hash_codegen::common::AtomicOrdering,
        _size: hash_source::Size,
    ) -> Self::Value {
        todo!()
    }

    fn load_operand(
        &mut self,
        _place: hash_codegen::lower::place::PlaceRef<Self::Value>,
    ) -> hash_codegen::lower::operands::OperandRef<Self::Value> {
        todo!()
    }

    fn store(
        &mut self,
        _value: Self::Value,
        _ptr: Self::Value,
        _alignment: hash_codegen::target::alignment::Alignment,
    ) -> Self::Value {
        todo!()
    }

    fn store_with_flags(
        &mut self,
        _value: Self::Value,
        _ptr: Self::Value,
        _alignment: hash_codegen::target::alignment::Alignment,
        _flags: hash_codegen::common::MemFlags,
    ) -> Self::Value {
        todo!()
    }

    fn atomic_store(
        &mut self,
        _value: Self::Value,
        _ptr: Self::Value,
        _alignment: hash_codegen::target::alignment::Alignment,
        _ordering: hash_codegen::common::AtomicOrdering,
    ) -> Self::Value {
        todo!()
    }

    fn get_element_pointer(
        &mut self,
        _ty: Self::Type,
        _ptr: Self::Value,
        _indices: &[Self::Value],
    ) -> Self::Value {
        todo!()
    }

    fn bounded_get_element_pointer(
        &mut self,
        _ty: Self::Type,
        _ptr: Self::Value,
        _indices: &[Self::Value],
    ) -> Self::Value {
        todo!()
    }

    fn structural_get_element_pointer(
        &mut self,
        _ty: Self::Type,
        _ptr: Self::Value,
        _index: u64,
    ) -> Self::Value {
        todo!()
    }

    fn memcpy(
        &mut self,
        _destination: (Self::Value, hash_codegen::target::alignment::Alignment),
        _source: (Self::Value, hash_codegen::target::alignment::Alignment),
        _size: Self::Value,
        _flags: hash_codegen::common::MemFlags,
    ) {
        todo!()
    }

    fn memmove(
        &mut self,
        _destination: (Self::Value, hash_codegen::target::alignment::Alignment),
        _source: (Self::Value, hash_codegen::target::alignment::Alignment),
        _size: Self::Value,
        _flags: hash_codegen::common::MemFlags,
    ) {
        todo!()
    }

    fn memset(
        &mut self,
        _ptr: Self::Value,
        _fill: Self::Value,
        _size: Self::Value,
        _align: hash_codegen::target::alignment::Alignment,
        _flags: hash_codegen::common::MemFlags,
    ) {
        todo!()
    }

    fn select(
        &mut self,
        _condition: Self::Value,
        _then: Self::Value,
        _otherwise: Self::Value,
    ) -> Self::Value {
        todo!()
    }

    fn extract_field_value(&mut self, _value: Self::Value, _field_index: usize) -> Self::Value {
        todo!()
    }

    fn insert_field_value(
        &mut self,
        _value: Self::Value,
        _element: Self::Value,
        _index: usize,
    ) -> Self::Value {
        todo!()
    }

    fn lifetime_start(&mut self, _ptr: Self::Value, _size: hash_source::Size) {
        todo!()
    }

    fn lifetime_end(&mut self, _ptr: Self::Value, _size: hash_source::Size) {
        todo!()
    }

    fn add_range_metadata_to(
        &mut self,
        _value: Self::Value,
        _range: hash_codegen::target::abi::ValidScalarRange,
    ) {
        todo!()
    }
}
