//! IR Optimisation pass that aims at removing un-used [Local]s
//! within a particular graph. This involves checking the following
//! properties:
//!
//! 1. Count how many times the [Local] is used as an [RValue].
//!
//! 2. For any [Local]s that are to be removed, we also remove all
//!    assignments to those locals that may affect counts of other
//!   [Local]s.

use hash_ir::{
    ir::{
        Body, IrRef, Local, LocalDecl, Place, PlaceProjection, RValue, Statement, StatementKind,
        RETURN_PLACE,
    },
    visitor::{walk_mut, IrVisitorMut, ModifyingIrVisitor, PlaceContext},
    IrCtx,
};
use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};
use index_vec::{index_vec, IndexVec};

use super::IrOptimisationPass;

/// The [CleanupLocalPass] is responsible for removing un-used [Local]s
/// from a given [Body]. This removes any assignments to dead locals, and
/// re-orders all of the used locals to have valid indices after that
/// pass is completed.
pub struct CleanupLocalPass;

impl IrOptimisationPass for CleanupLocalPass {
    fn name(&self) -> &'static str {
        "cleanup_locals"
    }

    /// Pass [CleanupLocalPass] is always enabled since it performs
    /// necessary cleanup of the initially generated IR.
    fn enabled(&self, settings: &CompilerSettings) -> bool {
        settings.optimisation_level >= OptimisationLevel::Debug
    }

    fn optimise(&self, body: &mut Body, store: &IrCtx) {
        let mut local_map = LocalUseMap::new(body, store);
        self.simplify_locals(body, &mut local_map);

        // after the locals are simplified, we need to re-map all of the
        // ones so that we can trim all of them from the body declaration.
        let local_remaps = local_map.remap_locals(&mut body.declarations);

        if local_remaps.iter().any(Option::is_none) {
            // create an updater, and then we can remap all of the places.
            let updater = LocalUpdater::new(local_remaps, store);
            updater.visit(body);

            body.declarations.shrink_to_fit();
        }
    }
}

impl CleanupLocalPass {
    /// This is the main algorithm of this pass. We have already constructed a
    /// [LocalUseMap] which denotes how many times each [Local] is used as an
    /// [RValue] within the [Body]. We then iterate over all of the [Statement]s
    /// and check whether the [Local] that they reference on the left-hand side
    /// is not used. If it is not used, then we can remove the statement.
    /// However, the removal of the statement may affect the counts of other
    /// [Local]s, so we need to update the counts for each [Local] that we
    /// see. This is done by re-visiting the statement that was removed, and
    /// decrementing the count for each [Local] that we see in that
    /// particular statement.
    fn simplify_locals(&self, body: &mut Body, local_map: &mut LocalUseMap<'_>) {
        let mut changed = true;

        while changed {
            changed = false;

            // iterate all blocks and remove any dead local references
            for block in body.basic_blocks.blocks_mut() {
                block.statements.retain(|statement| {
                    let (keep, is_nop) = match statement.kind {
                        StatementKind::Nop => (false, true),
                        StatementKind::Assign(place, _) | StatementKind::Discriminate(place, _)
                            if !local_map.is_used(place.local) =>
                        {
                            (false, false)
                        }
                        _ => (true, false),
                    };

                    if !keep {
                        // If we removed a `nop`, then we don't have to re-run the
                        // whole graph since this does not affect the counts of any
                        // other locals.
                        if !is_nop {
                            // we also need to perform an update to the local count
                            // since we just removed the assignment to this local.
                            local_map.statement_removed(statement);
                        } else {
                            changed = true;
                        }
                    }

                    keep
                });
            }
        }
    }
}

/// A visitor that counts how many times each [Local] is used as an
/// [RValue] within a particular [Body].
pub struct LocalUseMap<'ir> {
    /// All of the counts for each local in the specified body.
    uses: Vec<usize>,

    /// The number of arguments that the body contains. We need
    /// to store this since we can't "eliminate" locals that represent
    /// the return value or the arguments of the function.
    arg_count: usize,

    /// Whether the count for each local use should be incremented,
    /// or whether it should be decremented. The count becomes decremented
    /// when a statement is removed from the control flow graph due to
    /// being dead code. This allows for the pass to avoid re-scanning
    /// the entire CFG after each local removal, and only what is needed
    /// for scanning.
    increment: bool,

    /// A reference to the [BodyDataStore] in order to access and
    /// read values references by the [Body].
    ctx: &'ir IrCtx,
}

impl<'ir> LocalUseMap<'ir> {
    /// Create a new [LocalUseMap] for the specified [Body].
    pub fn new(body: &Body, ctx: &'ir IrCtx) -> Self {
        let mut counts = vec![0; body.declarations.len()];

        // always set to `_0` to 1 since it is the return value and
        // is always used
        counts[RETURN_PLACE.index()] = 1;
        let mut this = Self { uses: counts, ctx, arg_count: body.arg_count, increment: true };

        // visit the body and record the counts for each local, then
        // return the
        this.visit(body);
        this
    }

    /// Check if a [Local] is used within the [Body] that was visited.
    pub fn is_used(&self, local: Local) -> bool {
        local.index() <= self.arg_count || self.uses[local.index()] != 0
    }

    /// Update the count for a [Local] based on whether the count
    /// should be incremented or decremented.
    fn update_count_for(&mut self, local: Local) {
        if self.increment {
            self.uses[local.index()] += 1;
        } else {
            debug_assert_ne!(self.uses[local.index()], 0);
            self.uses[local.index()] -= 1;
        }
    }

    /// When a [Statement] is removed from the [Body], we need to
    /// traverse the statement again, and update the counts for each
    /// local as we see them. However, rather than incrementing the counts
    /// for each local, we know decrement each item that we see.
    pub fn statement_removed(&mut self, statement: &Statement) {
        self.increment = false;

        // re-visit this particular statement since we've just removed it, use a
        // dummy reference since we don't care here.
        self.visit_statement(statement, IrRef::default());
    }

    /// Perform a remapping of the locals within the [Body] that was
    /// visited. This function will generate a map to remap each local
    /// to a possibly new local value. If the value is [None], then no
    /// remapping is required.
    pub fn remap_locals(
        &self,
        locals: &mut IndexVec<Local, LocalDecl>,
    ) -> IndexVec<Local, Option<Local>> {
        let mut remap = index_vec![None; self.uses.len()];
        let mut used = Local::new(0);

        // Iterate over each local, check if it is still alive, and it it isn't
        // then we need to remap it to `used`
        for alive_local in locals.indices() {
            if !self.is_used(alive_local) {
                continue;
            }

            // we swap the dead and alive indices, whilst also recording
            // that we need to remap the actual IR to the new local.
            remap[alive_local.index()] = Some(used);

            if alive_local != used {
                locals.swap(alive_local, used);
            }
            used += 1;
        }

        locals.truncate(used.index());
        remap
    }
}

impl<'ir> IrVisitorMut<'ir> for LocalUseMap<'ir> {
    fn ctx(&self) -> &'ir IrCtx {
        self.ctx
    }

    /// Visit an assignment [Statement], we only visit the [RValue] part of the
    /// assignment fully, and only check the projections of the [Place] in case
    /// it is referenced within a [PlaceProjection::Index].
    fn visit_assign_statement(&mut self, place: &Place, value: &RValue, reference: IrRef) {
        self.ctx().map_place(*place, |_, projections| {
            for projection in projections {
                if let PlaceProjection::Index(index_local) = projection {
                    self.update_count_for(*index_local);
                }
            }
        });

        // @@Safety: currently it is safe to remove all variants of an RValue, however
        // if we add more rvalues (specifically casts), then we might need to be
        // more careful about whether the rvalue is safe to remove or not.
        walk_mut::walk_rvalue(self, value, reference);
    }

    /// This function will update the count for the referenced local in this
    /// place. We don't count places that "assign something" since this does
    /// not inherently use the local.
    fn visit_local(&mut self, local: Local, _: PlaceContext, _: IrRef) {
        self.update_count_for(local);
    }
}

pub struct LocalUpdater<'ir> {
    /// The map of locals to remap to a new local. If the [Local] index is
    /// [None], this means that the local is dead and was removed. If the
    /// [Local] index is [Some], then the local was not removed and should
    /// be remapped to the new [Local].
    remap: IndexVec<Local, Option<Local>>,

    /// Reference to body data store
    store: &'ir IrCtx,
}

impl<'ir> LocalUpdater<'ir> {
    /// Create a new [LocalUpdater].
    pub fn new(remap: IndexVec<Local, Option<Local>>, store: &'ir IrCtx) -> Self {
        Self { remap, store }
    }
}

impl<'ir> ModifyingIrVisitor<'ir> for LocalUpdater<'ir> {
    fn store(&self) -> &'ir IrCtx {
        self.store
    }

    /// Perform a remapping of the [Local] within the [Place] to a new [Local].
    fn visit_local(&self, local: &mut Local, _: PlaceContext, _: IrRef) {
        if let Some(new_local) = self.remap[*local] {
            *local = new_local;
        }
    }
}
