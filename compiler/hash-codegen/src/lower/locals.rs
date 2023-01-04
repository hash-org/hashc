//! This module contains all of the logic that is
//! dedicated to analysing all of the declared locals within
//! an IR body, and whether they can be allocated on the stack
//! or not.

use fixedbitset::FixedBitSet;
use hash_ir::{
    ir::{self, IrRef, Local, START_BLOCK},
    traversal,
    visitor::IrVisitorMut,
};
use hash_utils::graph::dominators::Dominators;
use index_vec::IndexVec;

use super::FnBuilder;
use crate::traits::{ctx::HasCtxMethods, layout::LayoutMethods, CodeGen};

pub fn compute_non_ssa_locals<'b, 'ir, Builder: CodeGen<'b>>(
    fn_builder: &FnBuilder<'b, 'ir, Builder>,
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

struct LocalKindAnalyser<'ir, 'b, Builder: CodeGen<'b>> {
    /// The function lowering context.
    fn_builder: &'ir FnBuilder<'b, 'ir, Builder>,

    /// The [Dominator]s of the the function body.
    dominators: Dominators<ir::BasicBlock>,

    /// A map that represents what kind of "memory" is needed to
    /// represent the local, an allocation or can be passed around
    /// as a scalar value.
    locals: IndexVec<Local, LocalMemoryKind>,
}

impl<'ir, 'b, Builder: CodeGen<'b>> LocalKindAnalyser<'ir, 'b, Builder> {
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

impl<'ir, 'b, Builder: CodeGen<'b>> IrVisitorMut<'ir> for LocalKindAnalyser<'ir, 'b, Builder> {
    fn store(&self) -> &'ir hash_ir::BodyDataStore {
        self.fn_builder.ctx.body_data()
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
            self.visit_place(place, reference);
        }

        self.visit_rvalue(value, reference);
    }

    fn visit_place(&mut self, _place: &ir::Place, _reference: IrRef) {}

    fn visit_local(&mut self, _: Local, _reference: IrRef) {}
}
