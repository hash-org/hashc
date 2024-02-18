//! Module contains all of the logic that involves optimising the
//! generated IR bodies of various items from the source. Each optimisation
//! pass is implemented as a function that takes a mutable reference to a
//! `Body` and may modify the body by removing, or adding instructions and
//! or basic blocks.
//!
//! @@Todo: write a constant value propagation pass.

use hash_ir::{ir::Body, IrCtx};
use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};
use hash_utils::timing::{CellStageMetrics, HasMetrics};

// Various passes that are used to optimise the generated IR bodies.
mod cleanup_locals;
mod simplify_graph;

pub trait IrOptimisationPass {
    /// Get the name of the particular optimisation pass.
    fn name(&self) -> &'static str;

    /// Check if this optimisation pas is enabled with accordance to
    /// the current [LoweringSettings].
    fn enabled(&self, settings: &CompilerSettings) -> bool {
        settings.optimisation_level > OptimisationLevel::Debug
    }

    /// Perform the optimisation pass on the body.
    fn optimise(&self, body: &mut Body, store: &IrCtx);
}

/// The optimiser is responsible for running all of the optimisation passes.
/// Since all bodies are already lowered, and they have no interdependencies,
/// we can run all of the optimisation passes on each body in parallel.
pub struct Optimiser<'ir> {
    store: &'ir IrCtx,

    /// Stores all of the lowering settings that are used to
    /// determine which passes are enabled.
    settings: &'ir CompilerSettings,

    /// The various passes that have been added to the optimisation
    /// pipeline.
    passes: Vec<Box<dyn IrOptimisationPass + Send>>,

    /// Metrics for each of the passes.
    metrics: CellStageMetrics,
}

impl<'ir> Optimiser<'ir> {
    pub fn new(store: &'ir IrCtx, settings: &'ir CompilerSettings) -> Self {
        Self {
            store,
            settings,
            passes: vec![
                Box::new(simplify_graph::SimplifyGraphPass),
                Box::new(cleanup_locals::CleanupLocalPass),
            ],
            metrics: CellStageMetrics::default(),
        }
    }

    /// Optimise a specific body. This will run all of the optimisation passes
    /// on the body.
    pub fn optimise(&self, body: &mut Body) {
        for pass in self.passes.iter() {
            if pass.enabled(self.settings) {
                self.time_item(pass.name(), |this| {
                    pass.optimise(body, this.store);
                })
            }
        }
    }

    pub fn into_metrics(self) -> CellStageMetrics {
        self.metrics
    }
}

impl HasMetrics for Optimiser<'_> {
    fn metrics(&self) -> &CellStageMetrics {
        &self.metrics
    }
}
