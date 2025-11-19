//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![feature(decl_macro, never_type, unwrap_infallible)]

mod build;
mod cfg;
mod ctx;

mod discover;
mod optimise;
mod ty;

use build::BodyBuilder;
use ctx::BuilderCtx;
use discover::FnDiscoverer;
use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_ir::{
    IrStorage,
    call_graph::{CallGraph, CallGraphWriter},
};
use hash_ir_utils::{graphviz::IrGraphWriter, pretty::IrPrettyWriter};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage, StageMetrics},
    settings::{CompilerSettings, CompilerStageKind, IrDumpMode},
    workspace::{SourceStageInfo, Workspace},
};
use hash_repr::{LayoutStorage, compute::LayoutComputer};
use hash_semantics::storage::SemanticStorage;
use hash_source::SourceId;
use hash_storage::store::{Store, statics::StoreId};
use hash_tir::{stores::tir_stores, tir::HasAstNodeId};
use hash_utils::{log, profiling::HasMutMetrics, rayon};
use optimise::Optimiser;

/// The Hash IR builder compiler stage.
#[derive(Default)]
pub struct IrGen {
    /// The metrics of the IR builder.
    metrics: StageMetrics,
}

impl HasMutMetrics for IrGen {
    fn metrics(&mut self) -> &mut StageMetrics {
        &mut self.metrics
    }
}

/// The [LoweringCtx] represents all of the required information
/// that the [IrGen] stage needs to query from the pipeline
/// in order to perform its lowering operations.
pub struct LoweringCtx<'ir> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ir mut Workspace,

    /// The settings of the current session.
    pub settings: &'ir CompilerSettings,

    /// Reference to the semantic storage that comes from
    /// the typechecking compiler phase.
    pub semantic_storage: &'ir SemanticStorage,

    /// Reference to the IR storage that is used to store
    /// the lowered IR, and all metadata about the IR.
    pub icx: &'ir mut IrStorage,

    /// Reference to the [LayoutStorage] that is used to store
    /// the layouts of types.
    pub lcx: &'ir LayoutStorage,

    /// Reference to the rayon thread pool.
    pub _pool: &'ir rayon::ThreadPool,
}

pub trait LoweringCtxQuery: CompilerInterface {
    fn data(&mut self) -> LoweringCtx<'_>;
}

impl<Ctx: LoweringCtxQuery> CompilerStage<Ctx> for IrGen {
    /// Return that this is [CompilerStageKind::Lower].
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Lower
    }

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone()
    }

    fn reset_metrics(&mut self) {
        self.metrics = StageMetrics::default();
    }

    /// Lower that AST of each module that is currently in the workspace
    /// into Hash IR. This will iterate over all modules, and possibly
    /// interactive statements to see if the need IR lowering, if so they
    /// are lowered and the result is saved on the [IrStorage].
    /// Additionally, this module is responsible for performing
    /// optimisations on the IR (if specified via the [CompilerSettings]).
    fn run(&mut self, _entry: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let data = ctx.data();

        let entry_point = &data.semantic_storage.distinguished_items.entry_point;

        // Discover all of the bodies that need to be lowered
        let items = self.record("discover", |_| {
            let discoverer = FnDiscoverer::new(&data.workspace.source_stage_info);
            discoverer.discover_fns()
        });

        // Pre-allocate the vector of lowered bodies.
        let mut lowered_bodies = Vec::with_capacity(items.fns.len());

        self.record("build", |_| {
            for func in items.into_iter() {
                let name = func.borrow().name.ident();

                let ctx = BuilderCtx::new(&data);
                let mut builder = BodyBuilder::new(name, func.into(), ctx);
                builder.build();

                let body = builder.finish();

                // This is the entry point, so we need to record that this
                // is the entry point.
                if let Some(def) = entry_point.def()
                    && def == func
                {
                    let instance = body.meta.ty().borrow().as_instance();
                    data.icx.entry_point.set(instance, entry_point.kind().unwrap());
                }

                // add the body to the lowered bodies
                lowered_bodies.push(body);
            }
        });

        // Mark all modules now as lowered, and all generated
        // bodies to the store.
        data.workspace.source_stage_info.set_all(SourceStageInfo::LOWERED);
        data.icx.add_bodies(lowered_bodies);

        Ok(())
    }

    fn cleanup(&mut self, _entry: SourceId, ctx: &mut Ctx) {
        let data = ctx.data();
        let builder = BuilderCtx::new(&data);

        // Iterate over all of the ADTs that have a registered `AstNodeId`
        // in the `AstInfo`. If the ADT contains a `#layout_of` attribute,
        // then we try to lower the type, and then print the layout of
        // the type.
        //
        // @@Todo: instead of looping through all the data defs, we should
        // instead look at a queue of data defs which should have been constructed
        // earlier.
        tir_stores().data_def().for_each_entry(|data_def| {
            if let Some(id) = data_def.node_id()
                && attr_store().node_has_attr(id, attrs::LAYOUT_OF)
            {
                builder.dump_ty_layout(data_def)
            }
        })
    }
}

/// Compiler stage that is responsible for performing optimisations on the
/// Hash IR. This will iterate over all of the bodies that have been generated
/// and perform optimisations on them based on if they are applicable and the
/// current configuration settings of the compiler.
#[derive(Default)]
pub struct IrOptimiser {
    /// The metrics of the IR optimiser.
    metrics: StageMetrics,
}

impl HasMutMetrics for IrOptimiser {
    fn metrics(&mut self) -> &mut StageMetrics {
        &mut self.metrics
    }
}

impl<Ctx: LoweringCtxQuery> CompilerStage<Ctx> for IrOptimiser {
    /// Return that this is [CompilerStageKind::Lower].
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Lower
    }

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone()
    }

    fn reset_metrics(&mut self) {
        self.metrics = StageMetrics::default();
    }

    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let LoweringCtx { icx, settings, .. } = ctx.data();

        let bodies = &mut icx.bodies;
        let body_data = &icx.ctx;

        self.record("optimise", |this| {
            // @@Todo: think about making optimisation passes in parallel...
            // pool.scope(|scope| {
            //     for body in &mut icx.generated_bodies {
            //         scope.spawn(|_| {
            //             let optimiser = Optimiser::new(body_data, settings);
            //             optimiser.optimise(body);
            //         });
            //     }
            // });

            for body in bodies.iter_mut() {
                let optimiser = Optimiser::new(body_data, settings);
                optimiser.optimise(body);

                // Collect metrics on the stages.
                let metrics = optimiser.into_metrics().into();
                this.metrics().merge(&metrics);
            }
        });

        Ok(())
    }

    fn cleanup(&mut self, _entry_point: SourceId, ctx: &mut Ctx) {
        let LoweringCtx { icx, settings, lcx, .. } = ctx.data();

        // Build the call graph
        if settings.lowering_settings.show_call_graph {
            let call_graph = CallGraph::build(icx.bodies.iter().as_slice());
            let writer = CallGraphWriter::with_default_options(call_graph);
            log::info!("call graph:\n{}", writer);
        }

        // we need to check if any of the bodies have been marked for `dumping`
        // and emit the IR that they have generated.
        let dump = settings.lowering_settings.dump;
        let quiet_prelude = settings.prelude_is_quiet;

        let lc = LayoutComputer::new(lcx);

        let mut bodies_to_dump = vec![];

        // Find all the bodies that we want to dump
        for body in icx.bodies.iter() {
            // Skip the prelude if we're in quiet mode
            if quiet_prelude && body.source().is_prelude() {
                continue;
            }

            // Check if we need to print this body (or if we're printing all of them)
            // and then skip bodies that we didn't request to print.
            if !dump && !body.needs_dumping() {
                continue;
            }

            bodies_to_dump.push(body);
        }

        if bodies_to_dump.is_empty() {
            return;
        }

        // @@Messaging: provide a format for the IR to be dumped in (which is public).

        if settings.lowering_settings.dump_mode == IrDumpMode::Graph {
            log::info!(
                "dumping IR in graphviz format:\n{}",
                IrGraphWriter::new(&bodies_to_dump, lc)
            );
        } else {
            log::info!("IR dump:\n{}", IrPrettyWriter::new(&bodies_to_dump, lc));
        }
    }
}
