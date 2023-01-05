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
        ConstOp, Local, Operand, Place, PlaceProjection, RValue, Statement, SwitchTargets,
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

    fn visit_basic_block(&mut self, _: BasicBlock, data: &BasicBlockData) {
        walk_mut::walk_basic_block(self, data);
    }

    fn visit_statement(&mut self, statement: &Statement) {
        walk_mut::walk_statement(self, statement);
    }

    fn visit_assign_statement(&mut self, place: &Place, value: &RValue) {
        walk_mut::walk_assign_statement(self, place, value);
    }

    fn visit_discriminator_statement(&mut self, place: &Place, variant: VariantIdx) {
        walk_mut::walk_discriminating_statement(self, place, variant);
    }

    fn visit_alloc_statement(&mut self, local: Local) {
        walk_mut::walk_alloc_statement(self, local);
    }

    fn visit_alloc_raw_statement(&mut self, local: Local) {
        walk_mut::walk_alloc_raw_statement(self, local);
    }

    fn visit_rvalue(&mut self, value: &RValue) {
        walk_mut::walk_rvalue(self, value);
    }

    fn visit_const_rvalue(&mut self, _: &ConstKind) {}

    fn visit_use_rvalue(&mut self, value: &Operand) {
        walk_mut::walk_use_rvalue(self, value);
    }

    fn visit_const_op_rvalue(&mut self, _: ConstOp, _: IrTyId) {}

    fn visit_unary_op_rvalue(&mut self, op: UnaryOp, value: &Operand) {
        walk_mut::walk_unary_op_rvalue(self, op, value);
    }

    fn visit_binary_op_rvalue(&mut self, op: BinOp, lhs: &Operand, rhs: &Operand) {
        walk_mut::walk_binary_op_rvalue(self, op, lhs, rhs);
    }

    fn visit_checked_binary_op_rvalue(&mut self, op: BinOp, lhs: &Operand, rhs: &Operand) {
        walk_mut::walk_checked_binary_op_rvalue(self, op, lhs, rhs);
    }

    fn visit_len_rvalue(&mut self, value: &Place) {
        walk_mut::walk_len_rvalue(self, value);
    }

    fn visit_ref_rvalue(&mut self, mutability: Mutability, value: &Place, mode: AddressMode) {
        walk_mut::walk_ref_rvalue(self, mutability, value, mode);
    }

    fn visit_aggregate_rvalue(&mut self, kind: AggregateKind, values: &[Operand]) {
        walk_mut::walk_aggregate_rvalue(self, kind, values);
    }

    fn visit_discriminant_rvalue(&mut self, value: &Place) {
        walk_mut::walk_discriminant_rvalue(self, value);
    }

    fn visit_terminator(&mut self, terminator: &Terminator) {
        walk_mut::walk_terminator(self, terminator);
    }

    fn visit_goto_terminator(&mut self, _: BasicBlock) {}

    fn visit_unreachable_terminator(&mut self) {}

    fn visit_return_terminator(&mut self) {}

    fn visit_call_terminator(
        &mut self,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlock>,
    ) {
        walk_mut::walk_call_terminator(self, op, args, destination, target);
    }

    fn visit_switch_terminator(&mut self, value: &Operand, targets: &SwitchTargets) {
        walk_mut::walk_switch_terminator(self, value, targets);
    }

    fn visit_assert_terminator(
        &mut self,
        condition: &Place,
        expected: bool,
        kind: AssertKind,
        target: BasicBlock,
    ) {
        walk_mut::walk_assert_terminator(self, condition, expected, kind, target);
    }

    fn visit_operand(&mut self, operand: &Operand) {
        walk_mut::walk_operand(self, operand);
    }

    fn visit_const_value(&mut self, _: &ConstKind) {}

    fn visit_place(&mut self, place: &Place) {
        walk_mut::walk_place(self, place);
    }

    fn visit_local(&mut self, _: Local) {}

    fn visit_projection(&mut self, projection: &PlaceProjection) {
        walk_mut::walk_projection(self, projection);
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
    pub fn walk_basic_block<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, data: &BasicBlockData) {
        for statement in data.statements.iter() {
            visitor.visit_statement(statement);
        }

        if let Some(terminator) = &data.terminator {
            visitor.visit_terminator(terminator);
        }
    }

    pub fn walk_statement<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, statement: &Statement) {
        match &statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => visitor.visit_assign_statement(place, value),

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, *variant)
            }
            StatementKind::Alloc(local) => visitor.visit_alloc_statement(*local),
            StatementKind::AllocRaw(local) => visitor.visit_alloc_raw_statement(*local),
        }
    }

    pub fn walk_assign_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        value: &RValue,
    ) {
        visitor.visit_place(place);
        visitor.visit_rvalue(value);
    }

    pub fn walk_discriminating_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        _: VariantIdx,
    ) {
        visitor.visit_place(place);
    }

    pub fn walk_alloc_statement<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, local: Local) {
        visitor.visit_local(local);
    }

    pub fn walk_alloc_raw_statement<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, local: Local) {
        visitor.visit_local(local);
    }

    pub fn walk_terminator<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, terminator: &Terminator) {
        match &terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(*target),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(),
            TerminatorKind::Return => visitor.visit_return_terminator(),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, *target)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, *expected, *kind, *target)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        _: Option<BasicBlock>,
    ) {
        visitor.visit_operand(op);
        args.iter().for_each(|arg| visitor.visit_operand(arg));
        visitor.visit_place(destination);
    }

    pub fn walk_switch_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        value: &Operand,
        _: &SwitchTargets,
    ) {
        visitor.visit_operand(value)
    }

    pub fn walk_assert_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        condition: &Place,
        _: bool,
        _: AssertKind,
        _: BasicBlock,
    ) {
        visitor.visit_place(condition)
    }

    pub fn walk_rvalue<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, value: &RValue) {
        match value {
            RValue::Use(place) => visitor.visit_use_rvalue(place),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(*op, *ty),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(*op, value),
            RValue::BinaryOp(op, operands) => {
                visitor.visit_binary_op_rvalue(*op, &operands.0, &operands.1)
            }
            RValue::CheckedBinaryOp(op, operand) => {
                visitor.visit_checked_binary_op_rvalue(*op, &operand.0, &operand.1)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(*mutability, place, *mode)
            }
            RValue::Aggregate(kind, values) => visitor.visit_aggregate_rvalue(*kind, values),
            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place),
        }
    }

    pub fn walk_use_rvalue<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, operand: &Operand) {
        visitor.visit_operand(operand)
    }

    pub fn walk_unary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: UnaryOp,
        value: &Operand,
    ) {
        visitor.visit_operand(value)
    }

    pub fn walk_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
    ) {
        visitor.visit_operand(lhs);
        visitor.visit_operand(rhs);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
    ) {
        visitor.visit_operand(lhs);
        visitor.visit_operand(rhs);
    }

    pub fn walk_len_rvalue<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, place: &Place) {
        visitor.visit_place(place)
    }

    pub fn walk_ref_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: Mutability,
        place: &Place,
        _: AddressMode,
    ) {
        visitor.visit_place(place)
    }

    pub fn walk_aggregate_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: AggregateKind,
        values: &[Operand],
    ) {
        values.iter().for_each(|value| visitor.visit_operand(value))
    }

    pub fn walk_discriminant_rvalue<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, place: &Place) {
        visitor.visit_place(place)
    }

    pub fn walk_operand<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, operand: &Operand) {
        match operand {
            Operand::Place(place) => visitor.visit_place(place),
            Operand::Const(constant) => visitor.visit_const_value(constant),
        }
    }

    pub fn walk_place<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, place: &Place) {
        visitor.visit_local(place.local);

        visitor.store().projections().map_fast(place.projections, |projection| {
            for projection in projection.iter() {
                visitor.visit_projection(projection)
            }
        })
    }

    pub fn walk_projection<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        projection: &PlaceProjection,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(*local)
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

    fn visit_basic_block(&self, _: BasicBlock, data: &mut BasicBlockData) {
        walk_modifying::walk_basic_block(self, data);
    }

    fn visit_statement(&self, statement: &mut Statement) {
        walk_modifying::walk_statement(self, statement);
    }

    fn visit_assign_statement(&self, place: &mut Place, value: &mut RValue) {
        walk_modifying::walk_assign_statement(self, place, value);
    }

    fn visit_discriminator_statement(&self, place: &mut Place, variant: &mut VariantIdx) {
        walk_modifying::walk_discriminating_statement(self, place, variant);
    }

    fn visit_alloc_statement(&self, local: &mut Local) {
        walk_modifying::walk_alloc_statement(self, local);
    }

    fn visit_alloc_raw_statement(&self, local: &mut Local) {
        walk_modifying::walk_alloc_raw_statement(self, local);
    }

    fn visit_rvalue(&self, value: &mut RValue) {
        walk_modifying::walk_rvalue(self, value);
    }

    fn visit_use_rvalue(&self, value: &mut Place) {
        walk_modifying::walk_use_rvalue(self, value);
    }

    fn visit_const_op_rvalue(&self, _: &mut ConstOp, _: &mut IrTyId) {}

    fn visit_unary_op_rvalue(&self, op: &mut UnaryOp, value: &mut Operand) {
        walk_modifying::walk_unary_op_rvalue(self, op, value);
    }

    fn visit_binary_op_rvalue(&self, op: &mut BinOp, lhs: &mut Operand, rhs: &mut Operand) {
        walk_modifying::walk_binary_op_rvalue(self, op, lhs, rhs);
    }

    fn visit_checked_binary_op_rvalue(&self, op: &mut BinOp, lhs: &mut Operand, rhs: &mut Operand) {
        walk_modifying::walk_checked_binary_op_rvalue(self, op, lhs, rhs);
    }

    fn visit_len_rvalue(&self, value: &mut Place) {
        walk_modifying::walk_len_rvalue(self, value);
    }

    fn visit_ref_rvalue(
        &self,
        mutability: &mut Mutability,
        value: &mut Place,
        mode: &mut AddressMode,
    ) {
        walk_modifying::walk_ref_rvalue(self, mutability, value, mode);
    }

    fn visit_aggregate_rvalue(&self, kind: &mut AggregateKind, values: &mut [Operand]) {
        walk_modifying::walk_aggregate_rvalue(self, kind, values);
    }

    fn visit_discriminant_rvalue(&self, value: &mut Place) {
        walk_modifying::walk_discriminant_rvalue(self, value);
    }

    fn visit_terminator(&self, terminator: &mut Terminator) {
        walk_modifying::walk_terminator(self, terminator);
    }

    fn visit_goto_terminator(&self, _: BasicBlock) {}

    fn visit_unreachable_terminator(&self) {}

    fn visit_return_terminator(&self) {}

    fn visit_call_terminator(
        &self,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        target: &mut Option<BasicBlock>,
    ) {
        walk_modifying::walk_call_terminator(self, op, args, destination, target);
    }

    fn visit_switch_terminator(&self, value: &mut Operand, targets: &mut SwitchTargets) {
        walk_modifying::walk_switch_terminator(self, value, targets);
    }

    fn visit_assert_terminator(
        &self,
        condition: &mut Place,
        expected: &mut bool,
        kind: &mut AssertKind,
        target: &mut BasicBlock,
    ) {
        walk_modifying::walk_assert_terminator(self, condition, expected, kind, target);
    }

    fn visit_operand(&self, operand: &mut Operand) {
        walk_modifying::walk_operand(self, operand);
    }

    fn visit_const_value(&self, _: &mut ConstKind) {}

    fn visit_place(&self, place: &mut Place) {
        walk_modifying::walk_place(self, place);
    }

    fn visit_local(&self, _: &mut Local) {}

    fn visit_projection(&self, projection: &mut PlaceProjection) {
        walk_modifying::walk_projection(self, projection);
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
        block: &mut BasicBlockData,
    ) {
        for statement in block.statements.iter_mut() {
            visitor.visit_statement(statement);
        }

        if let Some(terminator) = &mut block.terminator {
            visitor.visit_terminator(terminator);
        }
    }

    pub fn walk_statement<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, statement: &mut Statement) {
        match &mut statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => visitor.visit_assign_statement(place, value),

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, variant)
            }
            StatementKind::Alloc(local) => visitor.visit_alloc_statement(local),
            StatementKind::AllocRaw(local) => visitor.visit_alloc_raw_statement(local),
        }
    }

    pub fn walk_assign_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        value: &mut RValue,
    ) {
        visitor.visit_place(place);
        visitor.visit_rvalue(value);
    }

    pub fn walk_discriminating_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        _: &mut VariantIdx,
    ) {
        visitor.visit_place(place);
    }

    pub fn walk_alloc_statement<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, local: &mut Local) {
        visitor.visit_local(local);
    }

    pub fn walk_alloc_raw_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        local: &mut Local,
    ) {
        visitor.visit_local(local);
    }

    pub fn walk_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        terminator: &mut Terminator,
    ) {
        match &mut terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(*target),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(),
            TerminatorKind::Return => visitor.visit_return_terminator(),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, target)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, expected, kind, target)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        _: &mut Option<BasicBlock>,
    ) {
        visitor.visit_operand(op);
        args.iter_mut().for_each(|arg| visitor.visit_operand(arg));
        visitor.visit_place(destination);
    }

    pub fn walk_switch_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        value: &mut Operand,
        _: &mut SwitchTargets,
    ) {
        visitor.visit_operand(value)
    }

    pub fn walk_assert_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        condition: &mut Place,
        _: &mut bool,
        _: &mut AssertKind,
        _: &mut BasicBlock,
    ) {
        visitor.visit_place(condition)
    }

    pub fn walk_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, value: &mut RValue) {
        match value {
            RValue::Use(place) => visitor.visit_operand(place),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(op, ty),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(op, value),

            RValue::BinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_binary_op_rvalue(op, lhs, rhs)
            }
            RValue::CheckedBinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_checked_binary_op_rvalue(op, lhs, rhs)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(mutability, place, mode)
            }
            RValue::Aggregate(kind, values) => visitor.visit_aggregate_rvalue(kind, values),

            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place),
        }
    }

    pub fn walk_use_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, place: &mut Place) {
        visitor.visit_place(place)
    }

    pub fn walk_unary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut UnaryOp,
        value: &mut Operand,
    ) {
        visitor.visit_operand(value)
    }

    pub fn walk_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
    ) {
        visitor.visit_operand(lhs);
        visitor.visit_operand(rhs);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
    ) {
        visitor.visit_operand(lhs);
        visitor.visit_operand(rhs);
    }

    pub fn walk_len_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, place: &mut Place) {
        visitor.visit_place(place)
    }

    pub fn walk_ref_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut Mutability,
        place: &mut Place,
        _: &mut AddressMode,
    ) {
        visitor.visit_place(place)
    }

    pub fn walk_aggregate_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut AggregateKind,
        aggregate: &mut [Operand],
    ) {
        aggregate.iter_mut().for_each(|value| visitor.visit_operand(value))
    }

    pub fn walk_discriminant_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
    ) {
        visitor.visit_place(place)
    }

    pub fn walk_operand<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, operand: &mut Operand) {
        match operand {
            Operand::Place(place) => visitor.visit_place(place),
            Operand::Const(constant) => visitor.visit_const_value(constant),
        }
    }

    pub fn walk_place<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, place: &mut Place) {
        visitor.visit_local(&mut place.local);

        visitor.store().projections().modify_copied(place.projections, |projection| {
            for projection in projection.iter_mut() {
                visitor.visit_projection(projection)
            }
        })
    }

    pub fn walk_projection<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        projection: &mut PlaceProjection,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(local)
        }
    }
}

pub trait ModifyingIrVisitorMut<'ir> {
    /// Return a reference to the [BodyDataStore].
    fn storage(&self) -> &'ir BodyDataStore;
}
