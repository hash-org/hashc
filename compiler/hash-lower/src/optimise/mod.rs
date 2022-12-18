//! Module contains all of the logic that involves optimising the
//! generated IR bodies of various items from the source. Each optimisation
//! pass is implemented as a function that takes a mutable reference to a
//! `Body` and may modify the body by removing, or adding instructions and
//! or basic blocks.

use hash_ir::ir::Body;
use hash_pipeline::settings::LoweringSettings;
use hash_source::SourceMap;

// Various passes that are used to optimise the generated IR bodies.
mod simplify;

pub trait IrOptimisation {
    /// Check if this optimisation pas is enabled with accordance to
    /// the current [LoweringSettings].
    fn enabled(&self, settings: &LoweringSettings) -> bool;

    /// Perform the optimisation pass on the body.
    fn optimise(&self, body: &mut Body);
}

/// The optimiser is responsible for running all of the optimisation passes.
/// Since all bodies are already lowered, and they have no interdependencies,
/// we can run all of the optimisation passes on each body in parallel.
pub struct Optimiser<'ir> {
    /// The compiler source map.
    _source_map: &'ir SourceMap,

    /// Stores all of the lowering settings that are used to
    /// determine which passes are enabled.
    settings: LoweringSettings,

    /// The various passes that have been added to the optimisation
    /// pipeline.
    passes: Vec<Box<dyn IrOptimisation + Send>>,
}

impl<'ir> Optimiser<'ir> {
    pub fn new(source_map: &'ir SourceMap, settings: LoweringSettings) -> Self {
        Self { _source_map: source_map, settings, passes: vec![Box::new(simplify::SimplifyGraph)] }
    }

    /// Optimise a specific body. This will run all of the optimisation passes
    /// on the body.
    pub fn optimise(&self, body: &mut Body) {
        for pass in self.passes.iter() {
            if pass.enabled(&self.settings) {
                pass.optimise(body);
            }
        }
    }
}
