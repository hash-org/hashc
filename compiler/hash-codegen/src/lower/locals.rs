//! This module contains all of the logic that is
//! dedicated to analysing all of the declared locals within
//! an IR body, and whether they can be allocated on the stack
//! or not.

use fixedbitset::FixedBitSet;
use hash_ir::{
    ir::{self, IrRef, Local, PlaceProjection, START_BLOCK},
    traversal,
    visitor::{ImmutablePlaceContext, IrVisitorMut, MutablePlaceContext, PlaceContext},
};
use hash_layout::TyInfo;
use hash_utils::{
    graph::dominators::Dominators,
    store::{SequenceStore, SequenceStoreKey},
};
use index_vec::IndexVec;

use super::{operands::OperandRef, place::PlaceRef, FnBuilder};
use crate::traits::{
    builder::BlockBuilderMethods, ctx::HasCtxMethods, layout::LayoutMethods, CodeGen, CodeGenObject,
};

/// Defines what kind of reference a local has. A [LocalRef::Place]
/// is a reference to a stack allocation, and a [LocalRef::Operand]
/// is a reference to an immediate value.
pub enum LocalRef<V> {
    /// A reference to a stack allocation.
    Place(PlaceRef<V>),

    /// An immediate value. If this is not a ZST, then the `Value` is
    /// not present.
    Operand(Option<OperandRef<V>>),
}

impl<'b, V: CodeGenObject> LocalRef<V> {
    /// Create a new [LocalRef::Operand] instance.
    pub fn new_operand<Builder: CodeGen<'b, Value = V>>(
        builder: &mut Builder,
        layout: TyInfo,
    ) -> Self {
        if layout.is_zst(builder.layouts()) {
            LocalRef::Operand(Some(OperandRef::new_zst(builder, layout)))
        } else {
            LocalRef::Operand(None)
        }
    }
}

pub fn compute_non_ssa_locals<'b, Builder: BlockBuilderMethods<'b>>(
    fn_builder: &FnBuilder<'b, Builder>,
) -> FixedBitSet {
    let body = fn_builder.body;
    let dominators = body.basic_blocks.dominators();

    // pre-compute an initial value for each declared local
    // based on the type and layout parameters of the local.
    let locals = body
        .declarations
        .iter()
        .map(|local| {
            let ty = local.ty();
            let layout = fn_builder.ctx.layout_of_id(ty);

            if layout.is_zst(fn_builder.ctx.layouts()) {
                LocalMemoryKind::Zst
            } else if fn_builder.ctx.is_backend_immediate(layout) {
                LocalMemoryKind::Unused
            } else {
                LocalMemoryKind::Memory
            }
        })
        .collect();

    let mut analyser = LocalKindAnalyser { fn_builder, dominators, locals };

    // Arguments get assigned to by means of the function being called, and we
    // use the start location of the first block.
    for arg in body.args_iter() {
        let reference = START_BLOCK.ref_to_start();
        analyser.assign(arg, reference)
    }

    // If there exists a local definition that dominates all uses of that local,
    // the definition should be visited first. Traverse blocks in an order that
    // is a topological sort of dominance partial order.
    for (block, data) in traversal::PostOrder::new_from_start(body) {
        analyser.visit_basic_block(block, data);
    }

    // Create a map of all the locals that are used in the body and
    // whether they are SSA or not.
    let mut non_ssa_locals = FixedBitSet::with_capacity(body.declarations.len());

    // now iterate over all of the locals and determine whether they are non-ssa
    // or not.
    for (local, kind) in analyser.locals.iter_enumerated() {
        if matches!(kind, LocalMemoryKind::Memory) {
            non_ssa_locals.insert(local.index());
        }
    }

    non_ssa_locals
}

/// [LocalMemoryKind] is an enum that represents the kind of memory
/// is used for the [Local], whether it is a zero-sized type, whether
/// it requires an allocation, un-used or a single-use value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalMemoryKind {
    /// The local is a zero-sized type and does not require any memory.
    Zst,

    /// The local is a single-use value and does not require any memory.
    Unused,

    /// A [Local] that will require an allocation to be emitted when
    /// lowering.
    Memory,

    /// A scalar value that has a single definition and a single use
    /// in all block dominators.
    Ssa(ir::IrRef),
}

struct LocalKindAnalyser<'ir, 'b, Builder: BlockBuilderMethods<'b>> {
    /// The function lowering context.
    fn_builder: &'ir FnBuilder<'b, Builder>,

    /// The [Dominator]s of the the function body.
    dominators: Dominators<ir::BasicBlock>,

    /// A map that represents what kind of "memory" is needed to
    /// represent the local, an allocation or can be passed around
    /// as a scalar value.
    locals: IndexVec<Local, LocalMemoryKind>,
}

impl<'ir, 'b, Builder: BlockBuilderMethods<'b>> LocalKindAnalyser<'ir, 'b, Builder> {
    /// Perform an "assignment" to a particular local. This will
    /// change the previous kind of memory with the following rules:
    ///
    /// - If the previous kind of memory was a [LocalMemoryKind::Zst] or
    /// [LocalMemoryKind::Memory] then no changes occur since these cannot
    /// in any way be promoted.
    ///
    /// - If the previous kind of memory is [LocalMemoryKind::Unused] then it
    /// is converted into a [LocalMemoryKind::SSA] with an associated [IrRef].
    ///
    /// - If the previous kind of memory is [LocalMemoryKind::SSA] then it
    /// is converted into a [LocalMemoryKind::Memory] since it is no longer
    /// SSA.
    pub fn assign(&mut self, local: Local, reference: ir::IrRef) {
        let local_kind = &mut self.locals[local];

        match local_kind {
            LocalMemoryKind::Zst | LocalMemoryKind::Memory => {}
            LocalMemoryKind::Unused => {
                *local_kind = LocalMemoryKind::Ssa(reference);
            }
            LocalMemoryKind::Ssa(_) => {
                *local_kind = LocalMemoryKind::Memory;
            }
        }
    }
}

impl<'ir, 'b, Builder: BlockBuilderMethods<'b>> IrVisitorMut<'b>
    for LocalKindAnalyser<'ir, 'b, Builder>
{
    fn ctx(&self) -> &'b hash_ir::IrCtx {
        self.fn_builder.ctx.ir_ctx()
    }

    fn visit_assign_statement(&mut self, place: &ir::Place, value: &ir::RValue, reference: IrRef) {
        if let Some(local) = place.as_local() {
            self.assign(local, reference);

            // Short-circuit: if the RValue doesn't create an operand, i.e. an
            // aggregate value or a repeated value, then we can immediately
            // conclude that this will be in "memory"
            if self.locals[local] != LocalMemoryKind::Memory
                && !self.fn_builder.rvalue_creates_operand(value)
            {
                self.locals[local] = LocalMemoryKind::Memory;
            }
        } else {
            // we need to go the long way since projections might affect
            // the kind of memory that is used.
            self.visit_place(place, PlaceContext::Mutable(MutablePlaceContext::Store), reference);
        }

        self.visit_rvalue(value, reference);
    }

    fn visit_place(&mut self, place: &ir::Place, ctx: PlaceContext, reference: IrRef) {
        if place.projections.is_empty() {
            return self.visit_local(place.local, ctx, reference);
        }

        // If the place base type is a ZST then we can short-circuit
        // since they don't require any memory accesses.
        let base_ty = self.fn_builder.body.declarations[place.local].ty;
        let base_layout = self.fn_builder.ctx.layout_of_id(base_ty);

        if base_layout.is_zst(self.fn_builder.ctx.layouts()) {
            return;
        }

        // we want to check if any of the projections affect the
        // base local, if so then we need to check it as a local...
        let projections = self.fn_builder.ctx.ir_ctx().projections().get_vec(place.projections);

        let mut base_ctx = if ctx.is_mutating() {
            PlaceContext::Mutable(MutablePlaceContext::Projection)
        } else {
            PlaceContext::Immutable(ImmutablePlaceContext::Projection)
        };

        // @@Hack: in order to preserve the order of the traversal, we
        // save any locals that come from `Index` projections and then
        // traverse them after we have traversed the base local.
        let mut index_locals = vec![];

        // loop over the projections in reverse order
        for projection in projections.iter().rev() {
            // @@Todo: if the projection yields a ZST, then we can
            // also short-circuit here.

            // If the projection is a field, and the type of the
            // base can be represented as an immediate value, then
            // we use the `ctx` as the base context since this
            // is still an operand.
            match projection {
                PlaceProjection::Field(_) if ctx.is_operand() => {
                    if self.fn_builder.ctx.is_backend_immediate(base_layout) {
                        base_ctx = ctx;
                    }
                }
                PlaceProjection::Index(local) => {
                    index_locals.push(*local);
                }
                PlaceProjection::Field(_)
                | PlaceProjection::Downcast(_)
                | PlaceProjection::ConstantIndex { .. }
                | PlaceProjection::SubSlice { .. }
                | PlaceProjection::Deref => {}
            }
        }

        // Once we have determined the base context, we can now visit
        // the local.
        self.visit_local(place.local, base_ctx, reference);

        // now traverse the index locals, we set the `ctx` as being
        // an operand since they are always just being read in this
        // context.
        for local in index_locals {
            self.visit_local(
                local,
                PlaceContext::Immutable(ImmutablePlaceContext::Operand),
                reference,
            );
        }
    }

    fn visit_local(&mut self, local: Local, ctx: PlaceContext, reference: IrRef) {
        match ctx {
            // If it is being used as a destination for a value, then treat
            // it as an assignment
            PlaceContext::Mutable(MutablePlaceContext::Call) => {
                self.assign(local, reference);
            }

            PlaceContext::Immutable(ImmutablePlaceContext::Operand) => {
                match &mut self.locals[local] {
                    // @@Investigate: do we need to deal with in any way here?
                    LocalMemoryKind::Unused => {}

                    // ZSTs can disregard the rules, and memory values are already in memory.
                    LocalMemoryKind::Zst | LocalMemoryKind::Memory => {}
                    LocalMemoryKind::Ssa(def) if def.dominates(reference, &self.dominators) => {}

                    // If the value does not dominate the use, then it is no longer
                    // SSA and we need to convert it into a memory value.
                    kind @ LocalMemoryKind::Ssa(_) => {
                        *kind = LocalMemoryKind::Memory;
                    }
                }
            }

            // Everything else is a memory value.
            PlaceContext::Mutable(
                MutablePlaceContext::Store
                | MutablePlaceContext::Projection
                | MutablePlaceContext::Ref
                | MutablePlaceContext::Discriminant,
            )
            | PlaceContext::Immutable(
                ImmutablePlaceContext::Inspect
                | ImmutablePlaceContext::Ref
                | ImmutablePlaceContext::Projection,
            ) => {
                self.locals[local] = LocalMemoryKind::Memory;
            }
        }
    }
}
