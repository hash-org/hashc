//! IR Optimisation pass that aims at removing un-used [Local]s
//! within a particular graph. This involves checking the following
//! properties:
//!
//! 1. Count how many times the [Local] is used as an [RValue].
//!
//! 2. For any [Local]s that are to be removed, we also remove all
//!    assignments to those locals that may affect counts of other
//!   [Local]s.

use hash_ir::{ir::Body, BodyDataStore};
use hash_pipeline::settings::{LoweringSettings, OptimisationLevel};

use super::IrOptimisation;

/// The [CleanupLocalPass] is responsible for removing un-used [Local]s
/// from a given [Body]. This removes any assignments to dead locals, and
/// re-orders all of the used locals to have valid indices after that
/// pass is completed.
pub struct CleanupLocalPass;

impl IrOptimisation for CleanupLocalPass {
    fn name(&self) -> &'static str {
        "cleanup_locals"
    }

    /// Pass [CleanupLocalPass] is always enabled since it performs
    /// necessary cleanup of the initially generated IR.
    fn enabled(&self, settings: &LoweringSettings) -> bool {
        settings.optimisation_level >= OptimisationLevel::Debug
    }

    fn optimise(&self, _body: &mut Body, _store: &BodyDataStore) {
        // @@Todo: Need to implement an IR visitor in order to update
        // all locals that were shifted when others were removed.
    }
}
