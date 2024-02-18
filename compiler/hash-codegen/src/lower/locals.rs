//! This module contains all of the logic that is
//! dedicated to analysing all of the declared locals within
//! an IR body, and whether they can be allocated on the stack
//! or not.

use core::fmt;

use fixedbitset::FixedBitSet;
use hash_ir::{
    ir::{self, IrRef, Local, PlaceProjection, START_BLOCK},
    traversal,
    visitor::{ImmutablePlaceCtx, IrVisitorCtx, IrVisitorMut, MutablePlaceCtx, PlaceCtx},
};
use hash_repr::TyInfo;
use hash_storage::store::SequenceStoreKey;
use hash_utils::{graph::dominators::Dominators, index_vec::IndexVec};

use super::{operands::OperandRef, place::PlaceRef, FnBuilder};
use crate::traits::{builder::BlockBuilderMethods, layout::LayoutMethods, CodeGenObject};

/// Defines what kind of reference a local has. A [LocalRef::Place]
/// is a reference to a stack allocation, and a [LocalRef::Operand]
/// is a reference to an immediate value.
#[derive(Debug)]
pub enum LocalRef<V: std::fmt::Debug> {
    /// A reference to a stack allocation.
    Place(PlaceRef<V>),

    /// An immediate value. If this is not a ZST, then the `Value` is
    /// not present.
    Operand(Option<OperandRef<V>>),
}

impl<V: CodeGenObject> LocalRef<V> {
    /// Create a new [LocalRef::Operand] instance.
    pub fn new_operand(layout: TyInfo) -> Self {
        if layout.is_zst() {
            LocalRef::Operand(Some(OperandRef::zst(layout)))
        } else {
            LocalRef::Operand(None)
        }
    }
}

pub fn compute_non_ssa_locals<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    fn_builder: &FnBuilder<'a, 'b, Builder>,
) -> FixedBitSet {
    let body = fn_builder.body;
    let dominators = body.basic_blocks.dominators();

    // pre-compute an initial value for each declared local
    // based on the type and layout parameters of the local.
    let locals = body
        .locals
        .iter()
        .map(|local| {
            let ty = local.ty();
            let layout = fn_builder.ctx.layout_of(ty);

            if layout.is_zst() {
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

    let info = body.aux();

    // If there exists a local definition that dominates all uses of that local,
    // the definition should be visited first. Traverse blocks in an order that
    // is a topological sort of dominance partial order.
    for (block, data) in traversal::ReversePostOrder::new_from_start(body) {
        analyser.visit_basic_block(block, data, &info);
    }

    // Create a map of all the locals that are used in the body and
    // whether they are SSA or not.
    let mut non_ssa_locals = FixedBitSet::with_capacity(body.locals.len());

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

impl fmt::Display for LocalMemoryKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalMemoryKind::Zst => write!(f, "Zst"),
            LocalMemoryKind::Unused => write!(f, "Unused"),
            LocalMemoryKind::Memory => write!(f, "Memory"),
            LocalMemoryKind::Ssa(_) => write!(f, "Ssa"),
        }
    }
}

struct LocalKindAnalyser<'ir, 'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> {
    /// The function lowering context.
    fn_builder: &'ir FnBuilder<'a, 'b, Builder>,

    /// The [Dominator]s of the the function body.
    dominators: Dominators<ir::BasicBlock>,

    /// A map that represents what kind of "memory" is needed to
    /// represent the local, an allocation or can be passed around
    /// as a scalar value.
    locals: IndexVec<Local, LocalMemoryKind>,
}

impl<'ir, 'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> fmt::Display
    for LocalKindAnalyser<'ir, 'a, 'b, Builder>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // compute the longest local name, and align all of the
        // local names to that length.
        let width = self
            .locals
            .iter_enumerated()
            .fold(0, |acc, (local, _)| {
                if local.raw() == 0 {
                    return acc;
                }

                std::cmp::max(acc, local.raw().ilog10() + 1)
            })
            .try_into()
            .unwrap();

        for (local, kind) in self.locals.iter_enumerated() {
            writeln!(f, "{local: >width$?}: {kind}")?;
        }

        Ok(())
    }
}

impl<'ir, 'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> LocalKindAnalyser<'ir, 'a, 'b, Builder> {
    /// Perform an "assignment" to a particular local. This will
    /// change the previous kind of memory with the following rules:
    ///
    /// - If the previous kind of memory was a [LocalMemoryKind::Zst] or
    /// [LocalMemoryKind::Memory] then no changes occur since these cannot
    /// in any way be promoted.
    ///
    /// - If the previous kind of memory is [LocalMemoryKind::Unused] then it
    /// is converted into a [LocalMemoryKind::Ssa] with an associated [IrRef].
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

impl<'ir, 'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> IrVisitorMut<'ir>
    for LocalKindAnalyser<'ir, 'a, 'b, Builder>
{
    fn visit_assign_statement(
        &mut self,
        place: &ir::Place,
        value: &ir::RValue,
        ctx: &IrVisitorCtx<'_>,
    ) {
        if let Some(local) = place.as_local() {
            self.assign(local, ctx.location);

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
            self.visit_place(place, PlaceCtx::Mutable(MutablePlaceCtx::Store), ctx);
        }

        self.visit_rvalue(value, ctx);
    }

    fn visit_place(&mut self, place: &ir::Place, place_ctx: PlaceCtx, ctx: &IrVisitorCtx<'_>) {
        if place.projections.is_empty() {
            return self.visit_local(place.local, place_ctx, ctx.location);
        }

        // If the place base type is a ZST then we can short-circuit
        // since they don't require any memory accesses.
        let base_ty = self.fn_builder.body.locals[place.local].ty;
        let base_layout = self.fn_builder.ctx.layout_of(base_ty);

        if base_layout.is_zst() {
            return;
        }

        let mut base_ctx = if place_ctx.is_mutating() {
            PlaceCtx::Mutable(MutablePlaceCtx::Projection)
        } else {
            PlaceCtx::Immutable(ImmutablePlaceCtx::Projection)
        };

        // ##Hack: in order to preserve the order of the traversal, we
        // save any locals that come from `Index` projections and then
        // traverse them after we have traversed the base local.
        let mut index_locals = vec![];

        // loop over the projections in reverse order
        for projection in ctx.info.projections.borrow(place.projections).iter().rev() {
            // @@Todo: if the projection yields a ZST, then we can
            // also short-circuit here.

            // If the projection is a field, and the type of the
            // base can be represented as an immediate value, then
            // we use the `ctx` as the base context since this
            // is still an operand.
            match projection {
                PlaceProjection::Field(_) if place_ctx.is_operand() => {
                    if self.fn_builder.ctx.is_backend_immediate(base_layout) {
                        base_ctx = place_ctx;
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
        self.visit_local(place.local, base_ctx, ctx.location);

        // now traverse the index locals, we set the `ctx` as being
        // an operand since they are always just being read in this
        // context.
        for local in index_locals {
            self.visit_local(local, PlaceCtx::Immutable(ImmutablePlaceCtx::Operand), ctx.location);
        }
    }

    fn visit_local(&mut self, local: Local, ctx: PlaceCtx, reference: IrRef) {
        match ctx {
            // If it is being used as a destination for a value, then treat
            // it as an assignment
            PlaceCtx::Mutable(MutablePlaceCtx::Call) => {
                self.assign(local, reference);
            }

            // Don't do anything for meta context.
            PlaceCtx::Meta(_) => {}

            PlaceCtx::Immutable(ImmutablePlaceCtx::Operand) => {
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
            PlaceCtx::Mutable(
                MutablePlaceCtx::Store
                | MutablePlaceCtx::Projection
                | MutablePlaceCtx::Ref
                | MutablePlaceCtx::Discriminant,
            )
            | PlaceCtx::Immutable(
                ImmutablePlaceCtx::Inspect | ImmutablePlaceCtx::Ref | ImmutablePlaceCtx::Projection,
            ) => {
                self.locals[local] = LocalMemoryKind::Memory;
            }
        }
    }
}
