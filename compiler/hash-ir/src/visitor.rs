//! Hash IR visitor and walker trait definitions.

use crate::{
    ir::{
        AddressMode, AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp, Body, ConstKind,
        ConstOp, Local, Place, RValue, RValueId, Statement, SwitchTargets, Terminator,
    },
    ty::{IrTyId, Mutability, VariantIdx},
    BodyDataStore,
};

/// A trait for visiting the IR with a mutable context. This trait should
/// not be used for when modifications to the IR need to be made in place.
/// This is because the IR values are mapped from the [RValueStore] and
/// other stores in such a way that prevents in place modification. Any
/// modifications should be made by modifying the [RValue]s after the process
/// of visiting is complete or use the [ModifyingIrVisitor] trait families.
pub trait IrVisitorMut<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;

    /// Return the [Body] of the current visitor.
    fn body(&self) -> &'ir Body;

    type BodyRet;
    fn visit_body(&mut self, body: &'ir Body) -> Self::BodyRet;

    type BlockRet;
    fn visit_block(&mut self, block: &'ir BasicBlockData) -> Self::BlockRet;

    type StatementRet;
    fn visit_statement(&mut self, statement: &'ir Statement) -> Self::StatementRet;

    fn visit_nop_statement(&mut self) -> Self::StatementRet;

    fn visit_assign_statement(&mut self, place: &'ir Place, value: RValueId) -> Self::StatementRet;

    fn visit_discriminator_statement(
        &mut self,
        place: &'ir Place,
        variant: VariantIdx,
    ) -> Self::StatementRet;

    fn visit_alloc_statement(&mut self, local: Local) -> Self::StatementRet;

    fn visit_alloc_raw_statement(&mut self, local: Local) -> Self::StatementRet;

    type RValueRet;
    fn visit_rvalue(&mut self, value: &'ir RValue) -> Self::RValueRet;

    fn visit_const_rvalue(&mut self, value: &'ir ConstKind) -> Self::RValueRet;

    fn visit_use_rvalue(&mut self, value: &'ir Place) -> Self::RValueRet;

    fn visit_const_op_rvalue(&mut self, op: ConstOp, ty: IrTyId) -> Self::RValueRet;

    fn visit_checked_binary_op_rvalue(
        &mut self,
        op: BinOp,
        lhs: RValueId,
        rhs: RValueId,
    ) -> Self::RValueRet;

    fn visit_len_rvalue(&mut self, value: &'ir Place) -> Self::RValueRet;

    fn visit_ref_rvalue(
        &mut self,
        mutability: Mutability,
        value: &'ir Place,
        mode: AddressMode,
    ) -> Self::RValueRet;

    fn visit_aggregate_rvalue(
        &mut self,
        kind: AggregateKind,
        values: &'ir [RValueId],
    ) -> Self::RValueRet;

    fn visit_discriminant(&mut self, value: &'ir Place) -> Self::RValueRet;

    type TerminatorRet;
    fn visit_terminator(&mut self, terminator: &'ir Terminator) -> Self::TerminatorRet;

    fn visit_goto_terminator(&mut self, target: BasicBlock) -> Self::TerminatorRet;

    fn visit_unreachable_terminator(&mut self) -> Self::TerminatorRet;

    fn visit_return_terminator(&mut self) -> Self::TerminatorRet;

    fn visit_call_terminator(
        &mut self,
        op: RValueId,
        args: &'ir [RValueId],
        destination: &'ir Place,
        target: Option<BasicBlock>,
    ) -> Self::TerminatorRet;

    fn visit_switch_terminator(
        &mut self,
        value: RValueId,
        targets: &'ir SwitchTargets,
    ) -> Self::TerminatorRet;

    fn visit_assert_terminator(
        &mut self,
        condition: &'ir Place,
        expected: bool,
        kind: AssertKind,
        target: BasicBlock,
    ) -> Self::TerminatorRet;

    type PlaceRet;
    fn visit_place(&mut self, place: &'ir Place) -> Self::PlaceRet;
}

// @@Todo: fill these in when the general structure of `IrVisitorMut` is
// finalised.
pub trait IrVisitor<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;

    /// Return the [Body] of the current visitor.
    fn body(&self) -> &'ir Body;
}

pub trait ModifyingIrVisitor<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;

    /// Return the [Body] of the current visitor.
    fn body(&self) -> &'ir Body;
}

pub trait ModifyingIrVisitorMut<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;

    /// Return the [Body] of the current visitor.
    fn body(&self) -> &'ir Body;
}
