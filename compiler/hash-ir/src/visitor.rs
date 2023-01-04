//! Hash IR visitor and walker trait definitions.
//!
//! In an ideal world, this should be generated using a similar
//! approach to as the AST. Most of the time, we don't want to
//! write the visitor code by hand. Ideally, we want:
//!
//! 1. A cartesian product of the IR Visitor traits, so that we
//!    can both visit with a mutable and immutable context, and an
//!    a visitor that can modify the IR in place and one that can't.
//!
//! 2. The ability to generate walking methods for the IR that can accompany
//!    all variants fo the visiting traits.
//!
//! 3. The ability to hide away the boilerplate of the visitor and walking
//!    code for nodes that don't need to be dealt with.
use crate::{
    ir::{
        AddressMode, AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp, Body, ConstKind,
        ConstOp, IrRef, Local, Operand, Place, PlaceProjection, RValue, Statement, SwitchTargets,
        Terminator, UnaryOp,
    },
    ty::{IrTyId, Mutability, VariantIdx},
    BodyDataStore,
};

/// A trait for visiting the IR with a mutable context. This trait should
/// not be used for when modifications to the IR need to be made in place.
pub trait IrVisitorMut<'ir>: Sized {
    /// Return a reference to the [BodyDataStore].
    fn store(&self) -> &'ir BodyDataStore;

    /// The entry point of the visitor. This is called when the visitor
    /// is first initialised.
    fn visit(&mut self, body: &Body) {
        walk_mut::walk_body(self, body);
    }

    fn visit_basic_block(&mut self, block: BasicBlock, data: &BasicBlockData) {
        walk_mut::walk_basic_block(self, block, data);
    }

    fn visit_statement(&mut self, statement: &Statement, reference: IrRef) {
        walk_mut::walk_statement(self, statement, reference);
    }

    fn visit_assign_statement(&mut self, place: &Place, value: &RValue, reference: IrRef) {
        walk_mut::walk_assign_statement(self, place, value, reference);
    }

    fn visit_discriminator_statement(
        &mut self,
        place: &Place,
        variant: VariantIdx,
        reference: IrRef,
    ) {
        walk_mut::walk_discriminating_statement(self, place, variant, reference);
    }

    fn visit_alloc_statement(&mut self, local: Local, reference: IrRef) {
        walk_mut::walk_alloc_statement(self, local, reference);
    }

    fn visit_alloc_raw_statement(&mut self, local: Local, reference: IrRef) {
        walk_mut::walk_alloc_raw_statement(self, local, reference);
    }

    fn visit_rvalue(&mut self, value: &RValue, reference: IrRef) {
        walk_mut::walk_rvalue(self, value, reference);
    }

    fn visit_const_rvalue(&mut self, _: &ConstKind, _: IrRef) {}

    fn visit_use_rvalue(&mut self, value: &Operand, reference: IrRef) {
        walk_mut::walk_use_rvalue(self, value, reference);
    }

    fn visit_const_op_rvalue(&mut self, _: ConstOp, _: IrTyId, _: IrRef) {}

    fn visit_unary_op_rvalue(&mut self, op: UnaryOp, value: &Operand, reference: IrRef) {
        walk_mut::walk_unary_op_rvalue(self, op, value, reference);
    }

    fn visit_binary_op_rvalue(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        reference: IrRef,
    ) {
        walk_mut::walk_binary_op_rvalue(self, op, lhs, rhs, reference);
    }

    fn visit_checked_binary_op_rvalue(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        reference: IrRef,
    ) {
        walk_mut::walk_checked_binary_op_rvalue(self, op, lhs, rhs, reference);
    }

    fn visit_len_rvalue(&mut self, value: &Place, reference: IrRef) {
        walk_mut::walk_len_rvalue(self, value, reference);
    }

    fn visit_ref_rvalue(
        &mut self,
        mutability: Mutability,
        value: &Place,
        mode: AddressMode,
        reference: IrRef,
    ) {
        walk_mut::walk_ref_rvalue(self, mutability, value, mode, reference);
    }

    fn visit_aggregate_rvalue(
        &mut self,
        kind: AggregateKind,
        values: &[Operand],
        reference: IrRef,
    ) {
        walk_mut::walk_aggregate_rvalue(self, kind, values, reference);
    }

    fn visit_discriminant_rvalue(&mut self, value: &Place, reference: IrRef) {
        walk_mut::walk_discriminant_rvalue(self, value, reference);
    }

    fn visit_terminator(&mut self, terminator: &Terminator, reference: IrRef) {
        walk_mut::walk_terminator(self, terminator, reference);
    }

    fn visit_goto_terminator(&mut self, _: BasicBlock, _reference: IrRef) {}

    fn visit_unreachable_terminator(&mut self, _reference: IrRef) {}

    fn visit_return_terminator(&mut self, _reference: IrRef) {}

    fn visit_call_terminator(
        &mut self,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlock>,
        reference: IrRef,
    ) {
        walk_mut::walk_call_terminator(self, op, args, destination, target, reference);
    }

    fn visit_switch_terminator(
        &mut self,
        value: &Operand,
        targets: &SwitchTargets,
        reference: IrRef,
    ) {
        walk_mut::walk_switch_terminator(self, value, targets, reference);
    }

    fn visit_assert_terminator(
        &mut self,
        condition: &Place,
        expected: bool,
        kind: AssertKind,
        target: BasicBlock,
        reference: IrRef,
    ) {
        walk_mut::walk_assert_terminator(self, condition, expected, kind, target, reference);
    }

    fn visit_operand(&mut self, operand: &Operand, reference: IrRef) {
        walk_mut::walk_operand(self, operand, reference);
    }

    fn visit_const_value(&mut self, _: &ConstKind, _reference: IrRef) {}

    fn visit_place(&mut self, place: &Place, reference: IrRef) {
        walk_mut::walk_place(self, place, reference);
    }

    fn visit_local(&mut self, _: Local, _reference: IrRef) {}

    fn visit_projection(&mut self, projection: &PlaceProjection, reference: IrRef) {
        walk_mut::walk_projection(self, projection, reference);
    }
}

/// Contains all of the walking methods for the [IrVisitorMut] trait.
pub mod walk_mut {
    use hash_utils::store::SequenceStore;

    use super::{IrVisitorMut, *};
    use crate::ir::{StatementKind, TerminatorKind};

    /// Walk over all the [BasicBlock]s in the [Body] of the given
    /// to the visitor.
    pub fn walk_body<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, body: &Body) {
        for (block, data) in body.blocks().iter_enumerated() {
            visitor.visit_basic_block(block, data);
        }
    }

    /// Walk over all the [Statement]s in the given [BasicBlock] to the
    pub fn walk_basic_block<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        block: BasicBlock,
        data: &BasicBlockData,
    ) {
        let mut index = 0;
        for statement in data.statements.iter() {
            let reference = IrRef::new(block, index);
            visitor.visit_statement(statement, reference);
            index += 1;
        }

        if let Some(terminator) = &data.terminator {
            let reference = IrRef::new(block, index);
            visitor.visit_terminator(terminator, reference);
        }
    }

    pub fn walk_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        statement: &Statement,
        reference: IrRef,
    ) {
        match &statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => {
                visitor.visit_assign_statement(place, value, reference)
            }

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, *variant, reference)
            }
            StatementKind::Alloc(local) => visitor.visit_alloc_statement(*local, reference),
            StatementKind::AllocRaw(local) => visitor.visit_alloc_raw_statement(*local, reference),
        }
    }

    pub fn walk_assign_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        value: &RValue,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference);
        visitor.visit_rvalue(value, reference);
    }

    pub fn walk_discriminating_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        _: VariantIdx,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference);
    }

    pub fn walk_alloc_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        local: Local,
        reference: IrRef,
    ) {
        visitor.visit_local(local, reference);
    }

    pub fn walk_alloc_raw_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        local: Local,
        reference: IrRef,
    ) {
        visitor.visit_local(local, reference);
    }

    pub fn walk_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        terminator: &Terminator,
        reference: IrRef,
    ) {
        match &terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(*target, reference),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(reference),
            TerminatorKind::Return => visitor.visit_return_terminator(reference),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, *target, reference)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets, reference)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, *expected, *kind, *target, reference)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        _: Option<BasicBlock>,
        reference: IrRef,
    ) {
        visitor.visit_operand(op, reference);
        args.iter().for_each(|arg| visitor.visit_operand(arg, reference));
        visitor.visit_place(destination, reference);
    }

    pub fn walk_switch_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        value: &Operand,
        _: &SwitchTargets,
        reference: IrRef,
    ) {
        visitor.visit_operand(value, reference)
    }

    pub fn walk_assert_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        condition: &Place,
        _: bool,
        _: AssertKind,
        _: BasicBlock,
        reference: IrRef,
    ) {
        visitor.visit_place(condition, reference)
    }

    pub fn walk_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        value: &RValue,
        reference: IrRef,
    ) {
        match value {
            RValue::Use(place) => visitor.visit_use_rvalue(place, reference),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(*op, *ty, reference),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(*op, value, reference),
            RValue::BinaryOp(op, operands) => {
                visitor.visit_binary_op_rvalue(*op, &operands.0, &operands.1, reference)
            }
            RValue::CheckedBinaryOp(op, operand) => {
                visitor.visit_checked_binary_op_rvalue(*op, &operand.0, &operand.1, reference)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place, reference),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(*mutability, place, *mode, reference)
            }
            RValue::Aggregate(kind, values) => {
                visitor.visit_aggregate_rvalue(*kind, values, reference)
            }
            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place, reference),
        }
    }

    pub fn walk_use_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        operand: &Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(operand, reference)
    }

    pub fn walk_unary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: UnaryOp,
        value: &Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(value, reference)
    }

    pub fn walk_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(lhs, reference);
        visitor.visit_operand(rhs, reference);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(lhs, reference);
        visitor.visit_operand(rhs, reference);
    }

    pub fn walk_len_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_ref_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: Mutability,
        place: &Place,
        _: AddressMode,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_aggregate_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: AggregateKind,
        values: &[Operand],
        reference: IrRef,
    ) {
        values.iter().for_each(|value| visitor.visit_operand(value, reference))
    }

    pub fn walk_discriminant_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_operand<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        operand: &Operand,
        reference: IrRef,
    ) {
        match operand {
            Operand::Place(place) => visitor.visit_place(place, reference),
            Operand::Const(constant) => visitor.visit_const_value(constant, reference),
        }
    }

    pub fn walk_place<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, place: &Place, reference: IrRef) {
        visitor.visit_local(place.local, reference);

        visitor.store().projections().map_fast(place.projections, |projection| {
            for projection in projection.iter() {
                visitor.visit_projection(projection, reference)
            }
        })
    }

    pub fn walk_projection<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        projection: &PlaceProjection,
        reference: IrRef,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(*local, reference)
        }
    }
}

pub trait ModifyingIrVisitor<'ir>: Sized {
    /// Return a reference to the [BodyDataStore].
    fn store(&self) -> &'ir BodyDataStore;

    /// The entry point of the visitor. This is called when the visitor
    /// is first initialised.
    fn visit(&self, body: &mut Body) {
        walk_modifying::walk_body(self, body);
    }

    fn visit_basic_block(&self, block: BasicBlock, data: &mut BasicBlockData) {
        walk_modifying::walk_basic_block(self, block, data);
    }

    fn visit_statement(&self, statement: &mut Statement, reference: IrRef) {
        walk_modifying::walk_statement(self, statement, reference);
    }

    fn visit_assign_statement(&self, place: &mut Place, value: &mut RValue, reference: IrRef) {
        walk_modifying::walk_assign_statement(self, place, value, reference);
    }

    fn visit_discriminator_statement(
        &self,
        place: &mut Place,
        variant: &mut VariantIdx,
        reference: IrRef,
    ) {
        walk_modifying::walk_discriminating_statement(self, place, variant, reference);
    }

    fn visit_alloc_statement(&self, local: &mut Local, reference: IrRef) {
        walk_modifying::walk_alloc_statement(self, local, reference);
    }

    fn visit_alloc_raw_statement(&self, local: &mut Local, reference: IrRef) {
        walk_modifying::walk_alloc_raw_statement(self, local, reference);
    }

    fn visit_rvalue(&self, value: &mut RValue, reference: IrRef) {
        walk_modifying::walk_rvalue(self, value, reference);
    }

    fn visit_use_rvalue(&self, value: &mut Place, reference: IrRef) {
        walk_modifying::walk_use_rvalue(self, value, reference);
    }

    fn visit_const_op_rvalue(&self, _: &mut ConstOp, _: &mut IrTyId, _reference: IrRef) {}

    fn visit_unary_op_rvalue(&self, op: &mut UnaryOp, value: &mut Operand, reference: IrRef) {
        walk_modifying::walk_unary_op_rvalue(self, op, value, reference);
    }

    fn visit_binary_op_rvalue(
        &self,
        op: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        reference: IrRef,
    ) {
        walk_modifying::walk_binary_op_rvalue(self, op, lhs, rhs, reference);
    }

    fn visit_checked_binary_op_rvalue(
        &self,
        op: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        reference: IrRef,
    ) {
        walk_modifying::walk_checked_binary_op_rvalue(self, op, lhs, rhs, reference);
    }

    fn visit_len_rvalue(&self, value: &mut Place, reference: IrRef) {
        walk_modifying::walk_len_rvalue(self, value, reference);
    }

    fn visit_ref_rvalue(
        &self,
        mutability: &mut Mutability,
        value: &mut Place,
        mode: &mut AddressMode,
        reference: IrRef,
    ) {
        walk_modifying::walk_ref_rvalue(self, mutability, value, mode, reference);
    }

    fn visit_aggregate_rvalue(
        &self,
        kind: &mut AggregateKind,
        values: &mut [Operand],
        reference: IrRef,
    ) {
        walk_modifying::walk_aggregate_rvalue(self, kind, values, reference);
    }

    fn visit_discriminant_rvalue(&self, value: &mut Place, reference: IrRef) {
        walk_modifying::walk_discriminant_rvalue(self, value, reference);
    }

    fn visit_terminator(&self, terminator: &mut Terminator, reference: IrRef) {
        walk_modifying::walk_terminator(self, terminator, reference);
    }

    fn visit_goto_terminator(&self, _: BasicBlock, _reference: IrRef) {}

    fn visit_unreachable_terminator(&self, _reference: IrRef) {}

    fn visit_return_terminator(&self, _reference: IrRef) {}

    fn visit_call_terminator(
        &self,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        target: &mut Option<BasicBlock>,
        reference: IrRef,
    ) {
        walk_modifying::walk_call_terminator(self, op, args, destination, target, reference);
    }

    fn visit_switch_terminator(
        &self,
        value: &mut Operand,
        targets: &mut SwitchTargets,
        reference: IrRef,
    ) {
        walk_modifying::walk_switch_terminator(self, value, targets, reference);
    }

    fn visit_assert_terminator(
        &self,
        condition: &mut Place,
        expected: &mut bool,
        kind: &mut AssertKind,
        target: &mut BasicBlock,
        reference: IrRef,
    ) {
        walk_modifying::walk_assert_terminator(self, condition, expected, kind, target, reference);
    }

    fn visit_operand(&self, operand: &mut Operand, reference: IrRef) {
        walk_modifying::walk_operand(self, operand, reference);
    }

    fn visit_const_value(&self, _: &mut ConstKind, _reference: IrRef) {}

    fn visit_place(&self, place: &mut Place, reference: IrRef) {
        walk_modifying::walk_place(self, place, reference);
    }

    fn visit_local(&self, _: &mut Local, _reference: IrRef) {}

    fn visit_projection(&self, projection: &mut PlaceProjection, reference: IrRef) {
        walk_modifying::walk_projection(self, projection, reference);
    }
}

/// Contains all of the walking methods for the [IrVisitorMut] trait.
pub mod walk_modifying {
    use hash_utils::store::SequenceStoreCopy;

    use super::{ModifyingIrVisitor, *};
    use crate::ir::{StatementKind, TerminatorKind};

    /// Walk over all the [BasicBlock]s in the [Body] of the given
    /// to the visitor.
    pub fn walk_body<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, body: &mut Body) {
        for (block, data) in body.basic_blocks.blocks_mut().iter_mut_enumerated() {
            visitor.visit_basic_block(block, data);
        }
    }

    /// Walk over all the [Statement]s in the given [BasicBlock] to the
    pub fn walk_basic_block<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        block: BasicBlock,
        data: &mut BasicBlockData,
    ) {
        let mut index = 0;

        for statement in data.statements.iter_mut() {
            let reference = IrRef::new(block, index);
            visitor.visit_statement(statement, reference);
            index += 1;
        }

        if let Some(terminator) = &mut data.terminator {
            let reference = IrRef::new(block, index);
            visitor.visit_terminator(terminator, reference);
        }
    }

    pub fn walk_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        statement: &mut Statement,
        reference: IrRef,
    ) {
        match &mut statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => {
                visitor.visit_assign_statement(place, value, reference)
            }

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, variant, reference)
            }
            StatementKind::Alloc(local) => visitor.visit_alloc_statement(local, reference),
            StatementKind::AllocRaw(local) => visitor.visit_alloc_raw_statement(local, reference),
        }
    }

    pub fn walk_assign_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        value: &mut RValue,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference);
        visitor.visit_rvalue(value, reference);
    }

    pub fn walk_discriminating_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        _: &mut VariantIdx,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference);
    }

    pub fn walk_alloc_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        local: &mut Local,
        reference: IrRef,
    ) {
        visitor.visit_local(local, reference);
    }

    pub fn walk_alloc_raw_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        local: &mut Local,
        reference: IrRef,
    ) {
        visitor.visit_local(local, reference);
    }

    pub fn walk_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        terminator: &mut Terminator,
        reference: IrRef,
    ) {
        match &mut terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(*target, reference),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(reference),
            TerminatorKind::Return => visitor.visit_return_terminator(reference),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, target, reference)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets, reference)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, expected, kind, target, reference)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        _: &mut Option<BasicBlock>,
        reference: IrRef,
    ) {
        visitor.visit_operand(op, reference);
        args.iter_mut().for_each(|arg| visitor.visit_operand(arg, reference));
        visitor.visit_place(destination, reference);
    }

    pub fn walk_switch_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        value: &mut Operand,
        _: &mut SwitchTargets,
        reference: IrRef,
    ) {
        visitor.visit_operand(value, reference)
    }

    pub fn walk_assert_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        condition: &mut Place,
        _: &mut bool,
        _: &mut AssertKind,
        _: &mut BasicBlock,
        reference: IrRef,
    ) {
        visitor.visit_place(condition, reference)
    }

    pub fn walk_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        value: &mut RValue,
        reference: IrRef,
    ) {
        match value {
            RValue::Use(place) => visitor.visit_operand(place, reference),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(op, ty, reference),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(op, value, reference),

            RValue::BinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_binary_op_rvalue(op, lhs, rhs, reference)
            }
            RValue::CheckedBinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_checked_binary_op_rvalue(op, lhs, rhs, reference)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place, reference),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(mutability, place, mode, reference)
            }
            RValue::Aggregate(kind, values) => {
                visitor.visit_aggregate_rvalue(kind, values, reference)
            }

            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place, reference),
        }
    }

    pub fn walk_use_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_unary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut UnaryOp,
        value: &mut Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(value, reference)
    }

    pub fn walk_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(lhs, reference);
        visitor.visit_operand(rhs, reference);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        reference: IrRef,
    ) {
        visitor.visit_operand(lhs, reference);
        visitor.visit_operand(rhs, reference);
    }

    pub fn walk_len_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_ref_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut Mutability,
        place: &mut Place,
        _: &mut AddressMode,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_aggregate_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut AggregateKind,
        aggregate: &mut [Operand],
        reference: IrRef,
    ) {
        aggregate.iter_mut().for_each(|value| visitor.visit_operand(value, reference))
    }

    pub fn walk_discriminant_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        reference: IrRef,
    ) {
        visitor.visit_place(place, reference)
    }

    pub fn walk_operand<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        operand: &mut Operand,
        reference: IrRef,
    ) {
        match operand {
            Operand::Place(place) => visitor.visit_place(place, reference),
            Operand::Const(constant) => visitor.visit_const_value(constant, reference),
        }
    }

    pub fn walk_place<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        reference: IrRef,
    ) {
        visitor.visit_local(&mut place.local, reference);

        visitor.store().projections().modify_copied(place.projections, |projection| {
            for projection in projection.iter_mut() {
                visitor.visit_projection(projection, reference)
            }
        })
    }

    pub fn walk_projection<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        projection: &mut PlaceProjection,
        reference: IrRef,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(local, reference)
        }
    }
}

pub trait ModifyingIrVisitorMut<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;
}
