//! Hash IR visitor and walker trait definitions.
//!
//! In an ideal world, this should be generated using a similar
//! approach to as the AST. Most of the time, we don't want to
//! write the visitor code by hand. Ideally, we want:
//!
//! 1. A cartesian product of the IR Visitor traits, so that we can both visit
//!    with a mutable and immutable context, and an a visitor that can modify
//!    the IR in place and one that can't.
//!
//! 2. The ability to generate walking methods for the IR that can accompany all
//!    variants fo the visiting traits.
//!
//! 3. The ability to hide away the boilerplate of the visitor and walking code
//!    for nodes that don't need to be dealt with.
use crate::{
    ir::{
        AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp, Body, BodyInfo, BodyInfoMut,
        Const, ConstOp, IrRef, Local, Operand, Place, PlaceProjection, RValue, Statement,
        SwitchTargets, Terminator, UnaryOp,
    },
    ty::{Mutability, RefKind, ReprTyId, VariantIdx},
};

/// A [PlaceCtx] is a reference of where a a particular [Place] is
/// being used. This is computed as the IR [Body] is being traversed.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PlaceCtx {
    /// Immutable context use.
    Immutable(ImmutablePlaceCtx),

    /// Mutable context use.
    Mutable(MutablePlaceCtx),

    /// Meta context use.
    Meta(MetaPlaceCtx),
}

impl PlaceCtx {
    /// Check whether the [PlaceContext] is mutating
    pub fn is_mutating(self) -> bool {
        matches!(self, PlaceCtx::Mutable(_))
    }

    /// Check whether the [PlaceContext] is referring to
    /// an [Operand] context.
    pub fn is_operand(self) -> bool {
        matches!(self, PlaceCtx::Immutable(ImmutablePlaceCtx::Operand))
    }
}

/// [ImmutablePlaceCtx] is a reference of where a a particular [Place] is
/// being used in an immutable context.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ImmutablePlaceCtx {
    /// This [Place] is being loaded and read by something.
    Inspect,

    /// This [Place] is being used in an operand.
    Operand,

    /// The place is being used as a immutable reference.
    Ref,

    /// This [Place] is being used in an immutable projection.
    Projection,
}

/// [MutablePlaceCtx] is a reference of where a a particular [Place] is
/// being used in a mutable context.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MutablePlaceCtx {
    /// This [Place] occurs on the left hand side of an assignment.
    Store,

    /// This [Place] occurs on the left hand side of a statement with kind
    /// [`StatementKind::Discriminate`].
    Discriminant,

    /// This [Place] is being used as the destination value of a call
    /// instruction.
    Call,

    /// This [Place] is used as a base of a mutable projection.
    Projection,

    /// The place is being used as a mutable reference.
    Ref,
}

/// [MetaPlaceCtx] is a reference of where a a particular [Place] is
/// being used in a meta context. These contexts are only used within the
/// compiler to mark some information about the place, they have no runtime
/// implications.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MetaPlaceCtx {
    /// Used to mark a live interval for a [Place].
    Liveness,
}

pub struct IrVisitorCtx<'ctx> {
    pub location: IrRef,
    pub info: BodyInfo<'ctx>,
}

impl<'ctx> IrVisitorCtx<'ctx> {
    pub fn new(location: IrRef, info: BodyInfo<'ctx>) -> Self {
        Self { location, info }
    }
}

pub struct IrVisitorCtxMut<'ctx> {
    pub location: IrRef,
    pub info: BodyInfoMut<'ctx>,
}

impl<'ctx> IrVisitorCtxMut<'ctx> {
    pub fn new(location: IrRef, info: BodyInfoMut<'ctx>) -> Self {
        Self { location, info }
    }
}

/// A trait for visiting the IR with a mutable context. This trait should
/// not be used for when modifications to the IR need to be made in place.
pub trait IrVisitorMut<'ir>: Sized {
    /// The entry point of the visitor. This is called when the visitor
    /// is first initialised.
    fn visit(&mut self, body: &Body) {
        walk_mut::walk_body(self, body);
    }

    fn visit_basic_block(&mut self, block: BasicBlock, data: &BasicBlockData, info: &BodyInfo<'_>) {
        walk_mut::walk_basic_block(self, block, data, info);
    }

    fn visit_statement(&mut self, statement: &Statement, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_statement(self, statement, ctx);
    }

    fn visit_assign_statement(&mut self, place: &Place, value: &RValue, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_assign_statement(self, place, value, ctx);
    }

    fn visit_discriminator_statement(
        &mut self,
        place: &Place,
        variant: VariantIdx,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_discriminating_statement(self, place, variant, ctx);
    }

    fn visit_rvalue(&mut self, value: &RValue, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_rvalue(self, value, ctx);
    }

    fn visit_const_rvalue(&mut self, _: &Const, _: IrRef, _info: &BodyInfo<'_>) {}

    fn visit_use_rvalue(&mut self, value: &Operand, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_use_rvalue(self, value, ctx);
    }

    fn visit_const_op_rvalue(&mut self, _: ConstOp, _: ReprTyId, _: &IrVisitorCtx<'_>) {}

    fn visit_unary_op_rvalue(&mut self, op: UnaryOp, value: &Operand, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_unary_op_rvalue(self, op, value, ctx);
    }

    fn visit_binary_op_rvalue(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_binary_op_rvalue(self, op, lhs, rhs, ctx);
    }

    fn visit_checked_binary_op_rvalue(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_checked_binary_op_rvalue(self, op, lhs, rhs, ctx);
    }

    fn visit_len_rvalue(&mut self, value: &Place, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_len_rvalue(self, value, ctx);
    }

    fn visit_ref_rvalue(
        &mut self,
        mutability: Mutability,
        value: &Place,
        mode: RefKind,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_ref_rvalue(self, mutability, value, mode, ctx);
    }

    fn visit_aggregate_rvalue(
        &mut self,
        kind: AggregateKind,
        values: &[Operand],
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_aggregate_rvalue(self, kind, values, ctx);
    }

    fn visit_discriminant_rvalue(&mut self, value: &Place, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_discriminant_rvalue(self, value, ctx);
    }

    fn visit_terminator(&mut self, terminator: &Terminator, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_terminator(self, terminator, ctx);
    }

    fn visit_goto_terminator(&mut self, _: BasicBlock, _: &IrVisitorCtx<'_>) {}

    fn visit_unreachable_terminator(&mut self, _: &IrVisitorCtx<'_>) {}

    fn visit_return_terminator(&mut self, _: &IrVisitorCtx<'_>) {}

    fn visit_call_terminator(
        &mut self,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlock>,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_call_terminator(self, op, args, destination, target, ctx);
    }

    fn visit_switch_terminator(
        &mut self,
        value: &Operand,
        targets: &SwitchTargets,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_switch_terminator(self, value, targets, ctx);
    }

    fn visit_assert_terminator(
        &mut self,
        condition: &Operand,
        expected: bool,
        kind: &AssertKind,
        target: BasicBlock,
        ctx: &IrVisitorCtx<'_>,
    ) {
        walk_mut::walk_assert_terminator(self, condition, expected, kind, target, ctx);
    }

    fn visit_assert_kind(&mut self, kind: &AssertKind, ctx: &IrVisitorCtx<'_>) {
        match kind {
            AssertKind::DivisionByZero { operand } => {
                walk_mut::walk_operand(self, operand, ctx);
            }
            AssertKind::RemainderByZero { operand } => {
                walk_mut::walk_operand(self, operand, ctx);
            }
            AssertKind::Overflow { lhs, rhs, .. } => {
                walk_mut::walk_operand(self, lhs, ctx);
                walk_mut::walk_operand(self, rhs, ctx)
            }
            AssertKind::NegativeOverflow { operand } => {
                walk_mut::walk_operand(self, operand, ctx);
            }
            AssertKind::BoundsCheck { len, index } => {
                walk_mut::walk_operand(self, len, ctx);
                walk_mut::walk_operand(self, index, ctx);
            }
        }
    }

    fn visit_operand(&mut self, operand: &Operand, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_operand(self, operand, ctx);
    }

    fn visit_const_value(&mut self, _: &Const, _: &IrVisitorCtx<'_>) {}

    fn visit_place(&mut self, place: &Place, place_ctx: PlaceCtx, ctx: &IrVisitorCtx<'_>) {
        walk_mut::walk_place(self, place, place_ctx, ctx);
    }

    fn visit_local(&mut self, _: Local, _: PlaceCtx, _: IrRef) {}

    fn visit_projection(
        &mut self,
        projection: &PlaceProjection,
        place_ctx: PlaceCtx,
        location: IrRef,
    ) {
        walk_mut::walk_projection(self, projection, place_ctx, location);
    }
}

/// Contains all of the walking methods for the [IrVisitorMut] trait.
pub mod walk_mut {
    use super::{IrVisitorMut, *};
    use crate::ir::{BodyInfo, StatementKind, TerminatorKind};

    /// Walk over all the [BasicBlock]s in the [Body] of the given
    /// to the visitor.
    pub fn walk_body<'ir, V: IrVisitorMut<'ir>>(visitor: &mut V, body: &Body) {
        let info = body.aux();

        for (block, data) in body.basic_blocks.blocks.iter_enumerated() {
            visitor.visit_basic_block(block, data, &info);
        }
    }

    /// Walk over all the [Statement]s in the given [BasicBlock] to the
    pub fn walk_basic_block<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        block: BasicBlock,
        data: &BasicBlockData,
        info: &BodyInfo<'_>,
    ) {
        let mut index = 0;
        for statement in data.statements.iter() {
            let reference = IrRef::new(block, index);
            let ctx = IrVisitorCtx { location: reference, info: *info };
            visitor.visit_statement(statement, &ctx);
            index += 1;
        }

        if let Some(terminator) = &data.terminator {
            let reference = IrRef::new(block, index);
            let ctx = IrVisitorCtx { location: reference, info: *info };
            visitor.visit_terminator(terminator, &ctx);
        }
    }

    pub fn walk_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        statement: &Statement,
        ctx: &IrVisitorCtx<'_>,
    ) {
        match &statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => {
                visitor.visit_assign_statement(place, value, ctx)
            }

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, *variant, ctx)
            }
            StatementKind::Live(local) | StatementKind::Dead(local) => {
                visitor.visit_local(*local, PlaceCtx::Meta(MetaPlaceCtx::Liveness), ctx.location)
            }
        }
    }

    pub fn walk_assign_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        value: &RValue,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Mutable(MutablePlaceCtx::Store), ctx);
        visitor.visit_rvalue(value, ctx);
    }

    pub fn walk_discriminating_statement<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        _: VariantIdx,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Mutable(MutablePlaceCtx::Discriminant), ctx);
    }

    pub fn walk_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        terminator: &Terminator,
        ctx: &IrVisitorCtx<'_>,
    ) {
        match &terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(*target, ctx),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(ctx),
            TerminatorKind::Return => visitor.visit_return_terminator(ctx),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, *target, ctx)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets, ctx)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, *expected, kind, *target, ctx)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        op: &Operand,
        args: &[Operand],
        destination: &Place,
        _: Option<BasicBlock>,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(op, ctx);
        args.iter().for_each(|arg| visitor.visit_operand(arg, ctx));

        visitor.visit_place(destination, PlaceCtx::Mutable(MutablePlaceCtx::Call), ctx);
    }

    pub fn walk_switch_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        value: &Operand,
        _: &SwitchTargets,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(value, ctx)
    }

    pub fn walk_assert_terminator<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        condition: &Operand,
        _: bool,
        kind: &AssertKind,
        _: BasicBlock,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(condition, ctx);
        visitor.visit_assert_kind(kind, ctx);
    }

    pub fn walk_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        value: &RValue,
        ctx: &IrVisitorCtx<'_>,
    ) {
        match value {
            RValue::Use(place) => visitor.visit_use_rvalue(place, ctx),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(*op, *ty, ctx),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(*op, value, ctx),
            RValue::BinaryOp(op, operands) => {
                visitor.visit_binary_op_rvalue(*op, &operands.0, &operands.1, ctx)
            }
            RValue::CheckedBinaryOp(op, operand) => {
                visitor.visit_checked_binary_op_rvalue(*op, &operand.0, &operand.1, ctx)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place, ctx),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(*mutability, place, *mode, ctx)
            }
            RValue::Aggregate(kind, values) => visitor.visit_aggregate_rvalue(*kind, values, ctx),
            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place, ctx),
            RValue::Cast(_, operand, _) => visitor.visit_operand(operand, ctx),
            RValue::Repeat(operand, _) => visitor.visit_operand(operand, ctx),
        }
    }

    pub fn walk_use_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        operand: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(operand, ctx)
    }

    pub fn walk_unary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: UnaryOp,
        value: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(value, ctx)
    }

    pub fn walk_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(lhs, ctx);
        visitor.visit_operand(rhs, ctx);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_operand(lhs, ctx);
        visitor.visit_operand(rhs, ctx);
    }

    pub fn walk_len_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Inspect), ctx)
    }

    pub fn walk_ref_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        mutability: Mutability,
        place: &Place,
        _: RefKind,
        ctx: &IrVisitorCtx<'_>,
    ) {
        // @@Todo: do we need to have different contexts for different
        // kinds of refs?
        let place_ctx = match mutability {
            Mutability::Mutable => PlaceCtx::Mutable(MutablePlaceCtx::Ref),
            Mutability::Immutable => PlaceCtx::Immutable(ImmutablePlaceCtx::Ref),
        };

        visitor.visit_place(place, place_ctx, ctx)
    }

    pub fn walk_aggregate_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        _: AggregateKind,
        values: &[Operand],
        ctx: &IrVisitorCtx<'_>,
    ) {
        values.iter().for_each(|value| visitor.visit_operand(value, ctx))
    }

    pub fn walk_discriminant_rvalue<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Inspect), ctx)
    }

    pub fn walk_operand<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        operand: &Operand,
        ctx: &IrVisitorCtx<'_>,
    ) {
        match operand {
            Operand::Place(place) => {
                visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Operand), ctx)
            }
            Operand::Const(constant) => visitor.visit_const_value(constant, ctx),
        }
    }

    pub fn walk_place<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        place: &Place,
        place_ctx: PlaceCtx,
        ctx: &IrVisitorCtx<'_>,
    ) {
        visitor.visit_local(place.local, place_ctx, ctx.location);

        for projection in ctx.info.projections.borrow(place.projections) {
            visitor.visit_projection(projection, place_ctx, ctx.location)
        }
    }

    pub fn walk_projection<'ir, V: IrVisitorMut<'ir>>(
        visitor: &mut V,
        projection: &PlaceProjection,
        ctx: PlaceCtx,
        reference: IrRef,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(*local, ctx, reference)
        }
    }
}

pub trait ModifyingIrVisitor<'ir>: Sized {
    /// The entry point of the visitor. This is called when the visitor
    /// is first initialised.
    fn visit(&self, body: &'ir mut Body) {
        walk_modifying::walk_body(self, body);
    }

    fn visit_basic_block(
        &self,
        block: BasicBlock,
        data: &mut BasicBlockData,
        info: &mut BodyInfoMut<'ir>,
    ) {
        walk_modifying::walk_basic_block(self, block, data, info);
    }

    fn visit_statement(&self, statement: &mut Statement, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_statement(self, statement, ctx);
    }

    fn visit_assign_statement(
        &self,
        place: &mut Place,
        value: &mut RValue,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_assign_statement(self, place, value, ctx);
    }

    fn visit_discriminator_statement(
        &self,
        place: &mut Place,
        variant: &mut VariantIdx,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_discriminating_statement(self, place, variant, ctx);
    }

    fn visit_rvalue(&self, value: &mut RValue, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_rvalue(self, value, ctx);
    }

    fn visit_use_rvalue(&self, value: &mut Place, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_use_rvalue(self, value, ctx);
    }

    fn visit_const_op_rvalue(
        &self,
        _: &mut ConstOp,
        _: &mut ReprTyId,
        _: &mut IrVisitorCtxMut<'_>,
    ) {
    }

    fn visit_unary_op_rvalue(
        &self,
        op: &mut UnaryOp,
        value: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_unary_op_rvalue(self, op, value, ctx);
    }

    fn visit_binary_op_rvalue(
        &self,
        op: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_binary_op_rvalue(self, op, lhs, rhs, ctx);
    }

    fn visit_checked_binary_op_rvalue(
        &self,
        op: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_checked_binary_op_rvalue(self, op, lhs, rhs, ctx);
    }

    fn visit_len_rvalue(&self, value: &mut Place, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_len_rvalue(self, value, ctx);
    }

    fn visit_ref_rvalue(
        &self,
        mutability: &mut Mutability,
        value: &mut Place,
        mode: &mut RefKind,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_ref_rvalue(self, mutability, value, mode, ctx);
    }

    fn visit_aggregate_rvalue(
        &self,
        kind: &mut AggregateKind,
        values: &mut [Operand],
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_aggregate_rvalue(self, kind, values, ctx);
    }

    fn visit_discriminant_rvalue(&self, value: &mut Place, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_discriminant_rvalue(self, value, ctx);
    }

    fn visit_terminator(&self, terminator: &mut Terminator, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_terminator(self, terminator, ctx);
    }

    fn visit_goto_terminator(&self, _: &mut BasicBlock, _: &mut IrVisitorCtxMut<'_>) {}

    fn visit_unreachable_terminator(&self, _: &mut IrVisitorCtxMut<'_>) {}

    fn visit_return_terminator(&self, _: &mut IrVisitorCtxMut<'_>) {}

    fn visit_call_terminator(
        &self,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        target: &mut Option<BasicBlock>,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_call_terminator(self, op, args, destination, target, ctx);
    }

    fn visit_switch_terminator(
        &self,
        value: &mut Operand,
        targets: &mut SwitchTargets,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_switch_terminator(self, value, targets, ctx);
    }

    fn visit_assert_terminator(
        &self,
        condition: &mut Operand,
        expected: &mut bool,
        kind: &mut AssertKind,
        target: &mut BasicBlock,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        walk_modifying::walk_assert_terminator(self, condition, expected, kind, target, ctx);
    }

    fn visit_assert_kind(&self, kind: &mut AssertKind, ctx: &mut IrVisitorCtxMut<'_>) {
        match kind {
            AssertKind::DivisionByZero { operand } => {
                walk_modifying::walk_operand(self, operand, ctx);
            }
            AssertKind::RemainderByZero { operand } => {
                walk_modifying::walk_operand(self, operand, ctx);
            }
            AssertKind::Overflow { lhs, rhs, .. } => {
                walk_modifying::walk_operand(self, lhs, ctx);
                walk_modifying::walk_operand(self, rhs, ctx)
            }
            AssertKind::NegativeOverflow { operand } => {
                walk_modifying::walk_operand(self, operand, ctx);
            }
            AssertKind::BoundsCheck { len, index } => {
                walk_modifying::walk_operand(self, len, ctx);
                walk_modifying::walk_operand(self, index, ctx);
            }
        }
    }

    fn visit_operand(&self, operand: &mut Operand, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_operand(self, operand, ctx);
    }

    fn visit_const_value(&self, _: &mut Const, _: &mut IrVisitorCtxMut<'_>) {}

    fn visit_place(&self, place: &mut Place, place_ctx: PlaceCtx, ctx: &mut IrVisitorCtxMut<'_>) {
        walk_modifying::walk_place(self, place, place_ctx, ctx);
    }

    fn visit_local(&self, _: &mut Local, _ctx: PlaceCtx, _reference: IrRef) {}

    fn visit_projection(
        &self,
        projection: &mut PlaceProjection,
        place_ctx: PlaceCtx,
        reference: IrRef,
    ) {
        walk_modifying::walk_projection(self, projection, place_ctx, reference);
    }
}

/// Contains all of the walking methods for the [IrVisitorMut] trait.
pub mod walk_modifying {
    use super::{ModifyingIrVisitor, *};
    use crate::ir::{StatementKind, TerminatorKind};

    /// Walk over all the [BasicBlock]s in the [Body] of the given
    /// to the visitor.
    pub fn walk_body<'ir, V: ModifyingIrVisitor<'ir>>(visitor: &V, body: &'ir mut Body) {
        let Body { ref mut basic_blocks, ref mut locals, ref mut projections, .. } = body;
        let mut info = BodyInfoMut { locals, projections };

        for (block, data) in basic_blocks.blocks_mut().iter_mut_enumerated() {
            visitor.visit_basic_block(block, data, &mut info);
        }
    }

    /// Walk over all the [Statement]s in the given [BasicBlock] to the
    pub fn walk_basic_block<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        block: BasicBlock,
        data: &mut BasicBlockData,
        info: &mut BodyInfoMut<'_>,
    ) {
        let mut index = 0;
        let BodyInfoMut { ref mut locals, ref mut projections } = *info;

        for statement in data.statements.iter_mut() {
            let location = IrRef::new(block, index);
            let mut ctx = IrVisitorCtxMut::new(location, BodyInfoMut { locals, projections });
            visitor.visit_statement(statement, &mut ctx);
            index += 1;
        }

        if let Some(terminator) = &mut data.terminator {
            let location = IrRef::new(block, index);
            let mut ctx = IrVisitorCtxMut::new(location, BodyInfoMut { locals, projections });
            visitor.visit_terminator(terminator, &mut ctx);
        }
    }

    pub fn walk_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        statement: &mut Statement,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        match &mut statement.kind {
            StatementKind::Nop => {}
            StatementKind::Assign(place, value) => {
                visitor.visit_assign_statement(place, value, ctx)
            }

            StatementKind::Discriminate(place, variant) => {
                visitor.visit_discriminator_statement(place, variant, ctx)
            }
            StatementKind::Live(local) | StatementKind::Dead(local) => {
                visitor.visit_local(local, PlaceCtx::Meta(MetaPlaceCtx::Liveness), ctx.location)
            }
        }
    }

    pub fn walk_assign_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        value: &mut RValue,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Mutable(MutablePlaceCtx::Store), ctx);
        visitor.visit_rvalue(value, ctx);
    }

    pub fn walk_discriminating_statement<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        _: &mut VariantIdx,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Mutable(MutablePlaceCtx::Discriminant), ctx);
    }

    pub fn walk_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        terminator: &mut Terminator,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        match &mut terminator.kind {
            TerminatorKind::Goto(target) => visitor.visit_goto_terminator(target, ctx),
            TerminatorKind::Unreachable => visitor.visit_unreachable_terminator(ctx),
            TerminatorKind::Return => visitor.visit_return_terminator(ctx),
            TerminatorKind::Call { op, args, destination, target } => {
                visitor.visit_call_terminator(op, args, destination, target, ctx)
            }
            TerminatorKind::Switch { value, targets } => {
                visitor.visit_switch_terminator(value, targets, ctx)
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                visitor.visit_assert_terminator(condition, expected, kind, target, ctx)
            }
        }
    }

    pub fn walk_call_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        op: &mut Operand,
        args: &mut [Operand],
        destination: &mut Place,
        _: &mut Option<BasicBlock>,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        // visit the args and call operand
        visitor.visit_operand(op, ctx);
        args.iter_mut().for_each(|arg| visitor.visit_operand(arg, ctx));

        // visit the call destination place
        visitor.visit_place(destination, PlaceCtx::Mutable(MutablePlaceCtx::Call), ctx);
    }

    pub fn walk_switch_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        value: &mut Operand,
        _: &mut SwitchTargets,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_operand(value, ctx)
    }

    pub fn walk_assert_terminator<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        condition: &mut Operand,
        _: &mut bool,
        assert: &mut AssertKind,
        _: &mut BasicBlock,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_operand(condition, ctx);
        visitor.visit_assert_kind(assert, ctx);
    }

    pub fn walk_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        value: &mut RValue,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        match value {
            RValue::Use(place) => visitor.visit_operand(place, ctx),
            RValue::ConstOp(op, ty) => visitor.visit_const_op_rvalue(op, ty, ctx),
            RValue::UnaryOp(op, value) => visitor.visit_unary_op_rvalue(op, value, ctx),

            RValue::BinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_binary_op_rvalue(op, lhs, rhs, ctx)
            }
            RValue::CheckedBinaryOp(op, val) => {
                let (lhs, rhs) = val.as_mut();
                visitor.visit_checked_binary_op_rvalue(op, lhs, rhs, ctx)
            }
            RValue::Len(place) => visitor.visit_len_rvalue(place, ctx),
            RValue::Ref(mutability, place, mode) => {
                visitor.visit_ref_rvalue(mutability, place, mode, ctx)
            }
            RValue::Aggregate(kind, values) => visitor.visit_aggregate_rvalue(kind, values, ctx),

            RValue::Discriminant(place) => visitor.visit_discriminant_rvalue(place, ctx),
            RValue::Cast(_, operand, _) => visitor.visit_operand(operand, ctx),
            RValue::Repeat(operand, _) => visitor.visit_operand(operand, ctx),
        }
    }

    pub fn walk_use_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Operand), ctx)
    }

    pub fn walk_unary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut UnaryOp,
        value: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_operand(value, ctx)
    }

    pub fn walk_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_operand(lhs, ctx);
        visitor.visit_operand(rhs, ctx);
    }

    pub fn walk_checked_binary_op_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut BinOp,
        lhs: &mut Operand,
        rhs: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_operand(lhs, ctx);
        visitor.visit_operand(rhs, ctx);
    }

    pub fn walk_len_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Inspect), ctx)
    }

    pub fn walk_ref_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        mutability: &mut Mutability,
        place: &mut Place,
        _: &mut RefKind,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        // @@Todo: do we need to have different contexts for different
        // kinds of refs?
        let place_ctx = match mutability {
            Mutability::Mutable => PlaceCtx::Mutable(MutablePlaceCtx::Ref),
            Mutability::Immutable => PlaceCtx::Immutable(ImmutablePlaceCtx::Ref),
        };

        visitor.visit_place(place, place_ctx, ctx)
    }

    pub fn walk_aggregate_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        _: &mut AggregateKind,
        aggregate: &mut [Operand],
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        aggregate.iter_mut().for_each(|value| visitor.visit_operand(value, ctx))
    }

    pub fn walk_discriminant_rvalue<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Inspect), ctx)
    }

    pub fn walk_operand<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        operand: &mut Operand,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        match operand {
            Operand::Place(place) => {
                visitor.visit_place(place, PlaceCtx::Immutable(ImmutablePlaceCtx::Operand), ctx)
            }
            Operand::Const(constant) => visitor.visit_const_value(constant, ctx),
        }
    }

    pub fn walk_place<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        place: &mut Place,
        place_ctx: PlaceCtx,
        ctx: &mut IrVisitorCtxMut<'_>,
    ) {
        visitor.visit_local(&mut place.local, place_ctx, ctx.location);

        for projection in ctx.info.projections.borrow_mut(place.projections) {
            visitor.visit_projection(projection, place_ctx, ctx.location)
        }
    }

    pub fn walk_projection<'ir, V: ModifyingIrVisitor<'ir>>(
        visitor: &V,
        projection: &mut PlaceProjection,
        ctx: PlaceCtx,
        reference: IrRef,
    ) {
        if let PlaceProjection::Index(local) = projection {
            visitor.visit_local(local, ctx, reference)
        }
    }
}
