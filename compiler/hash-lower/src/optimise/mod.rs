//! Module contains all of the logic that involves optimising the
//! generated IR bodies of various items from the source. Each optimisation
//! pass is implemented as a function that takes a mutable reference to a
//! `Body` and may modify the body by removing, or adding instructions and
//! or basic blocks.
//!
//! @@Todo: write a constant value propagation pass.

use std::sync::Arc;

use hash_ir::{ir::Body, IrCtx};
use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};
use hash_source::SourceMap;

// Various passes that are used to optimise the generated IR bodies.
mod cleanup_locals;
mod simplify_graph;

pub trait IrOptimisationPass: Send + Sync {
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
    ctx: OptimiserCtx<'ir>,

    /// The various passes that have been added to the optimisation
    /// pipeline.
    passes: Arc<Vec<Box<dyn IrOptimisationPass + Send>>>,
}

#[derive(Clone)]
pub struct OptimiserCtx<'ir> {
    pub store: Arc<&'ir IrCtx>,

    /// The compiler source map.
    pub source_map: Arc<&'ir SourceMap>,

    /// Stores all of the lowering settings that are used to
    /// determine which passes are enabled.
    pub settings: Arc<&'ir CompilerSettings>,
}

impl<'ir> Optimiser<'ir> {
    /// Create a new instance of an optimiser.
    pub fn new(ctx: OptimiserCtx<'ir>) -> Self {
        Self {
            ctx,
            passes: Arc::new(vec![
                Box::new(simplify_graph::SimplifyGraphPass),
                Box::new(cleanup_locals::CleanupLocalPass),
            ]),
        }
    }

    /// Optimise a specific body. This will run all of the optimisation passes
    /// on the body.
    pub fn optimise(&self, body: &mut Body) {
        for pass in self.passes.iter() {
            if pass.enabled(self.ctx.settings.as_ref()) {
                pass.optimise(body, self.ctx.store.as_ref());
            }
        }
    }
}
