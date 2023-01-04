//! This module defines the core trait of the code generation backend
//! which is used to generate code for a particular backend. This trait
//! provides IR builder methods that the compiler uses to generate code
//! from Hash IR.

use std::sync::atomic::Ordering;

use hash_target::{
    abi::{AbiRepresentation, Scalar},
    alignment::Alignment,
};

use super::{
    ctx::HasCtxMethods, debug::BuildDebugInfoMethods, intrinsics::BuildIntrinsicCallMethods,
    target::HasTargetSpec, CodeGen,
};
use crate::{
    common::{CheckedOp, MemFlags},
    layout::LayoutId,
    lower::{operands::OperandRef, place::PlaceRef},
};

/// This trait defines all methods required to convert a Hash IR `BasicBlock`
/// into the backend equivalent.
pub trait BlockBuilderMethods<'a, 'b>:
    CodeGen<'b> + BuildIntrinsicCallMethods<'b> + BuildDebugInfoMethods + HasTargetSpec
{
    /// Function to build the given `BasicBlock` into the backend equivalent.
    fn build(ctx: &'a Self::CodegenCtx, block: Self::BasicBlock) -> Self;

    /// Get the current context
    fn ctx(&self) -> &Self::CodegenCtx;

    /// Create a new basic block within the current function.
    fn basic_block(&self) -> Self::BasicBlock;

    /// Add a block to the current function.
    fn append_block(&mut self, name: &str) -> Self::BasicBlock;

    /// Switch the current building context to the provided
    /// basic block.
    fn switch_to_block(&mut self, block: Self::BasicBlock);

    // --- Branching/Block termination ---

    /// Specify that the current block should return the specified value.
    fn return_value(&mut self, value: Self::Value);

    /// Specify that the current block should return void.
    fn return_void(&mut self);

    /// Branch from the current block to the specified destination block.
    fn branch(&mut self, destination: Self::BasicBlock);

    /// Conditionally branch on a `condition` value to either `true_block` or
    /// `false_block`.
    fn conditional_branch(
        &mut self,
        condition: Self::Value,
        true_block: Self::BasicBlock,
        false_block: Self::BasicBlock,
    );

    /// Switch on a `condition` value to one of the `blocks` based on the
    /// `values` that are matched.
    fn switch(
        &mut self,
        condition: Self::Value,
        cases: impl ExactSizeIterator<Item = (u128, Self::BasicBlock)>,
        otherwise_block: Self::BasicBlock,
    );

    /// Generate a function call as a terminator of the current block. A
    /// `checked_call` is a call that can throw an exception, and thus
    /// requires a `then_block` and `catch_block` to be specified. If a
    /// function call is not expected to throe an exception, then the
    /// `call` method should be used instead.
    ///
    /// @@Todo: deal with `fn_abi` parameters
    ///
    /// @@Todo: do we need to deal with funclets
    fn checked_call(
        &mut self,
        ty: Self::Type,
        args: &[Self::Value],
        then_block: Self::BasicBlock,
        catch_block: Self::BasicBlock,
    ) -> Self::Value;

    fn call(
        &mut self,
        ty: Self::Type,
        args: &[Self::Value],
        then_block: Self::BasicBlock,
    ) -> Self::Value;

    // --- Arithmetic ---

    /// Perform an addition operation on the given values.
    fn add(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a floating point addition operation on the given values.
    fn fadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a fast floating point addition operation on the given values.
    fn fadd_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a subtraction operation on the given values.
    fn sub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a floating point subtraction operation on the given values.
    fn fsub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a fast floating point subtraction operation on the given values.
    fn fsub_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a multiplication operation on the given values.
    fn mul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a floating point multiplication operation on the given values.
    fn fmul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a fast floating point multiplication operation on the given
    /// values.
    fn fmul_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unsigned division operation on the given values.
    fn udiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an exact unsigned division operation on the given values.
    fn exactudiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a signed division operation on the given values.
    fn sdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an exact signed division operation on the given values.
    fn exactsdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a floating point division operation on the given values.
    fn fdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a fast floating point division operation on the given values.
    fn fdiv_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unsigned remainder operation on the given values.
    fn urem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a signed remainder operation on the given values.
    fn srem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a floating point remainder operation on the given values.
    fn frem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a fast floating point remainder operation on the given values.
    fn frem_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a left shift operation on the given values.
    fn shl(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a logical right shift operation on the given values.
    fn lshr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an arithmetic right shift operation on the given values.
    fn ashr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked signed addition operation on the given values.
    fn unchecked_sadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked unsigned addition operation on the given values.
    fn unchecked_uadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked signed subtraction operation on the given values.
    fn unchecked_ssub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked unsigned subtraction operation on the given values.
    fn unchecked_usub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked signed multiplication operation on the given
    /// values.
    fn unchecked_smul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform an unchecked unsigned multiplication operation on the given
    /// values.
    fn unchecked_umul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a bitwise and operation on the given values.
    fn and(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a bitwise or operation on the given values.
    fn or(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a bitwise xor operation on the given values.
    fn xor(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    /// Perform a bitwise not operation on the given value.
    fn not(&mut self, v: Self::Value) -> Self::Value;

    /// Perform a negation operation on the given value.
    fn neg(&mut self, v: Self::Value) -> Self::Value;

    /// Perform a floating point negation operation on the given value.
    fn fneg(&mut self, v: Self::Value) -> Self::Value;

    /// Perform a checked binary operation on the given values. The [CheckedOp]s
    /// include either addition, multiplication, or subtraction.
    fn checked_bin_op(&mut self, op: CheckedOp, lhs: Self::Value, rhs: Self::Value) -> Self::Value;

    // --- Type conversions ---

    /// Perform a truncation from type of `value` to `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#trunc-to-instruction>
    fn truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// Perform a sign extension from type of `value` to `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#sext-to-instruction>
    fn sign_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// Perform a zero extension from type of `value` to `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#zext-to-instruction>
    fn zero_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fptoui` converts a floating-point value to its unsigned integer
    /// equivalent of type `dest_ty`.
    ///
    /// N.B. This performs a saturating conversion.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#fptoui-to-instruction>
    fn fp_to_ui_sat(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fptosi` converts a floating-point value to its signed integer
    /// equivalent of type `dest_ty`.
    ///
    /// N.B. This performs a saturating conversion.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#fptosi-to-instruction>
    fn fp_to_si_sat(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fptoui` converts a floating-point value to its unsigned integer
    /// equivalent of type `dest_ty`.
    ///
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#fptoui-to-instruction>
    fn fp_to_ui(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fptosi` converts a floating-point value to its signed integer
    /// equivalent of type `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#fptosi-to-instruction>
    fn fp_to_si(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `uitofp` converts an unsigned integer value to its floating-point
    /// equivalent of type `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#uitofp-to-instruction>
    fn ui_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `sitofp` converts a signed integer value to its floating-point
    /// equivalent of type `dest_ty`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#sitofp-to-instruction>
    fn si_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fptrunc` instruction converts a floating-point value to a
    /// floating-point value of smaller width.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#fptrunc-to-instruction>
    fn fp_truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `fpext` instruction converts a floating-point value to a
    /// floating-point value of larger width.
    fn fp_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    // --- Cast instructions and intrinsics ---

    /// The `ptrtoint` instruction converts a pointer value to an integer value.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#ptrtoint-to-instruction>
    fn ptr_to_int(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `inttoptr` instruction converts an integer value to a pointer value.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#inttoptr-to-instruction>
    fn int_to_ptr(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `bitcast` instruction converts a value from one type to another type
    /// without changing any bits.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#bitcast-to-instruction>
    fn bit_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    /// The `intcast` instruction converts a value from one integer type to
    /// another integer type.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#intcast-to-instruction>
    fn int_cast(&mut self, val: Self::Value, dest_ty: Self::Type, is_signed: bool) -> Self::Value;

    /// The `pointercast` instruction converts a value from one pointer type to
    /// another pointer type.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#addrspacecast-to-instruction>
    fn pointer_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value;

    // --- Intrinsic & Memory operations ---

    /// Take an immediate `i1` value and zero extend it to a boolean
    /// value.
    fn bool_from_immediate(&mut self, v: Self::Value) -> Self::Value;

    /// Convert a value to an immediate value of the given layout.
    fn to_immediate(&mut self, v: Self::Value, layout: LayoutId) -> Self::Value {
        if let AbiRepresentation::Scalar { kind } = self.layout_info(layout).abi {
            self.to_immediate_scalar(v, kind)
        } else {
            v
        }
    }

    /// Convert the given value to a [Scalar] value.
    fn to_immediate_scalar(&mut self, v: Self::Value, kind: Scalar) -> Self::Value;

    /// Create a store operation on the stack to given type and [Alignment]
    /// specification, returning a reference to the data location.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#alloca-instruction>
    fn alloca(&mut self, ty: Self::Type, alignment: Alignment) -> Self::Value;

    /// Allocate a byte array of a specified length and [Alignment] on the
    /// stack.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#alloca-instruction>
    fn byte_array_alloca(&mut self, len: Self::Value, alignment: Alignment) -> Self::Value;

    /// Write an [OperandRef] value repeatedly into a given destination.
    fn write_operand_repeatedly(
        &mut self,
        operand: OperandRef<Self::Value>,
        count: usize,
        destination: PlaceRef<Self::Value>,
    );

    /// Load a value from a given pointer of a type and a specified [Alignment].
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#load-instruction>
    fn load(&mut self, ty: Self::Type, ptr: Self::Value, alignment: Alignment) -> Self::Value;

    /// Emit an instruction for a volatile load from a given pointer of a type
    /// and a specified [Alignment].
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#load-instruction>
    fn volatile_load(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        alignment: Alignment,
    ) -> Self::Value;

    /// Emit an instruction for an atomic load from a given pointer of a type
    /// and a specified [Alignment].
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#load-instruction>
    fn atomic_load(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        alignment: Alignment,
    ) -> Self::Value;

    /// Emit an instruction to load an operand into a particular `place`.
    fn load_operand(&mut self, place: PlaceRef<Self::Value>) -> OperandRef<Self::Value>;

    /// Emit a `store` instruction to a given pointer of a type and a specified
    /// [Alignment].
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#store-instruction>
    fn store(&mut self, value: Self::Value, ptr: Self::Value, alignment: Alignment) -> Self::Value;

    /// Emit a `store` instruction with specified [MemFlags].
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#store-instruction>
    fn store_with_flags(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        flags: MemFlags,
    ) -> Self::Value;

    /// Emit an instruction for an atomic `store`.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#store-instruction>
    fn atomic_store(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        ordering: Ordering,
    ) -> Self::Value;

    /// Emit an instruction for a `gep` or `getelementptr` operation.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#getelementptr-instruction>
    fn get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value;

    /// Emit an instruction for a `gep` or `getelementptr` operation with
    /// the `inbounds` flag set as true. The exact semantics of `inbounds`
    /// is detailed in the LLVM language manual.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#getelementptr-instruction>
    fn bounded_get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value;

    /// Emit an instruction for a `gep` or `getelementptr` operation within
    /// an aggregate data structure. This will emit an instruction to get an
    /// element pointer with the specified field index.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#getelementptr-instruction>
    fn structural_get_element_pointer(ty: Self::Type, ptr: Self::Value, index: u64) -> Self::Value;

    /// Emit an instruction for a `memcpy` operation.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#llvm-memcpy-intrinsics>
    fn memcpy(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    );

    /// Emit an instruction for a `memmove` operation.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#llvm-memmove-intrinsics>
    fn memmove(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    );

    /// Emit an instruction for a `memset` operation.
    ///
    /// N.B. the `fill` argument is a `u8` value, not a pointer to a byte.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#llvm-memset-intrinsics>
    fn memset(
        &mut self,
        ptr: Self::Value,
        fill: Self::Value,
        size: Self::Value,
        align: Alignment,
        flags: MemFlags,
    );

    /// Emit an instruction for a `select` operation.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#select-instruction>
    fn select(
        &mut self,
        condition: Self::Value,
        then: Self::Value,
        otherwise: Self::Value,
    ) -> Self::Value;
}
