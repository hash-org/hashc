//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![feature(decl_macro, let_chains, never_type, unwrap_infallible)]

mod build;
mod cfg;

mod discover;
mod lower_ty;
mod optimise;

use build::{Builder, Tcx};
use discover::FnDiscoverer;
use hash_ir::{
    ty::IrTy,
    write::{graphviz, pretty},
    IrStorage,
};
use hash_layout::{compute::LayoutComputer, write::LayoutWriter, LayoutCtx, TyInfo};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerOutputStream, CompilerResult, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind, IrDumpMode},
    workspace::{SourceStageInfo, Workspace},
};
use hash_semantics::SemanticStorage;
use hash_source::{identifier::IDENTS, location::SourceLocation, SourceId};
use hash_tir::{
    data::DataTy,
    directives::DirectiveTarget,
    environment::{
        env::{AccessToEnv, Env},
        source_info::CurrentSourceInfo,
    },
    utils::common::CommonUtils,
};
use hash_utils::{
    store::{CloneStore, PartialStore, SequenceStore, Store},
    stream_writeln,
};
use lower_ty::TyLoweringCtx;
use optimise::Optimiser;

/// The Hash IR builder compiler stage.
#[derive(Default)]
pub struct IrGen;

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
    pub ir_storage: &'ir mut IrStorage,

    /// Reference to the [LayoutCtx] that is used to store
    /// the layouts of types.
    pub layout_storage: &'ir LayoutCtx,

    /// Reference to the output stream
    pub stdout: CompilerOutputStream,

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

    /// Lower that AST of each module that is currently in the workspace
    /// into Hash IR. This will iterate over all modules, and possibly
    /// interactive statements to see if the need IR lowering, if so they
    /// are lowered and the result is saved on the [IrStorage].
    /// Additionally, this module is responsible for performing
    /// optimisations on the IR (if specified via the [CompilerSettings]).
    fn run(&mut self, entry: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let LoweringCtx { semantic_storage, workspace, ir_storage, settings, .. } = ctx.data();
        let source_stage_info = &mut workspace.source_stage_info;

        let source_info = CurrentSourceInfo { source_id: entry };
        let env = Env::new(
            &semantic_storage.stores,
            &semantic_storage.context,
            &workspace.node_map,
            &workspace.source_map,
            &source_info,
        );

        let entry_point = &semantic_storage.entry_point;

        // Discover all of the bodies that need to be lowered
        let discoverer = FnDiscoverer::new(&env, source_stage_info);
        let items = discoverer.discover_fns();

        // Pre-allocate the vector of lowered bodies.
        let mut lowered_bodies = Vec::with_capacity(items.fns.len());

        for func in items.iter() {
            let symbol = discoverer.stores().fn_def().map_fast(*func, |func| func.name);
            let name = discoverer
                .stores()
                .symbol()
                .map_fast(symbol, |symbol| symbol.name.unwrap_or(IDENTS.underscore));

            // Get the source of the symbol therefore that way
            // we can get the source id of the function.
            let Some(SourceLocation { id, .. }) = discoverer.get_location(func) else {
                panic!("function `{name}` has no defined source location");
            };

            let tcx = Tcx::new(&env, semantic_storage);
            let mut builder =
                Builder::new(name, (*func).into(), id, tcx, &mut ir_storage.ctx, settings);
            builder.build();

            let body = builder.finish();

            // This is the entry point, so we need to record that this
            // is the entry point.
            if let Some(def) = entry_point.def() && def == *func {
                let IrTy::FnDef { instance } = ir_storage.ctx.tys().get(body.info.ty()) else {
                    panic!("entry point `{name}` is not a function definition");
                };

                ir_storage.entry_point.set(instance, entry_point.kind().unwrap());
            }

            // add the body to the lowered bodies
            lowered_bodies.push(body);
        }

        // Mark all modules now as lowered, and all generated
        // bodies to the store.
        source_stage_info.set_all(SourceStageInfo::LOWERED);
        ir_storage.add_bodies(lowered_bodies);

        Ok(())
    }

    fn cleanup(&mut self, entry: SourceId, stage_data: &mut Ctx) {
        let LoweringCtx {
            semantic_storage, ir_storage, layout_storage, workspace, mut stdout, ..
        } = stage_data.data();
        let source_info = CurrentSourceInfo { source_id: entry };
        let env = Env::new(
            &semantic_storage.stores,
            &semantic_storage.context,
            &workspace.node_map,
            &workspace.source_map,
            &source_info,
        );

        let ty_lowerer = TyLoweringCtx::new(
            &ir_storage.ctx,
            &env,
            semantic_storage.primitives_or_unset.get().unwrap(),
        );

        // @@Future: support generic substitutions here.
        let empty_args = semantic_storage.stores.args().create_empty();

        semantic_storage.stores.directives().internal_data().borrow().iter().for_each(|(id, directives)| {
            if directives.contains(IDENTS.layout_of) && let DirectiveTarget::DataDefId(data_def) = *id {
                let ty = ty_lowerer.ty_id_from_tir_data(DataTy { args: empty_args, data_def });
                let layout_computer = LayoutComputer::new(layout_storage, &ir_storage.ctx);

                // @@ErrorHandling: propagate this error if it occurs.
                if let Ok(layout) = layout_computer.layout_of_ty(ty) {
                    // Print the layout and add spacing between all of the specified layouts
                    // that were requested.
                    stream_writeln!(
                        stdout,
                        "{}",
                        LayoutWriter::new(TyInfo { ty, layout }, layout_computer)
                    );
                }
            }
        });
    }
}

/// Compiler stage that is responsible for performing optimisations on the
/// Hash IR. This will iterate over all of the bodies that have been generated
/// and perform optimisations on them based on if they are applicable and the
/// current configuration settings of the compiler.
#[derive(Default)]
pub struct IrOptimiser;

impl<Ctx: LoweringCtxQuery> CompilerStage<Ctx> for IrOptimiser {
    /// Return that this is [CompilerStageKind::Lower].
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Lower
    }

    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let LoweringCtx { workspace, ir_storage, settings, .. } = ctx.data();
        let source_map = &mut workspace.source_map;

        let bodies = &mut ir_storage.bodies;
        let body_data = &ir_storage.ctx;
        // let optimiser = Optimiser::new(ir_storage, source_map, settings);

        // @@Todo: think about making optimisation passes in parallel...
        // pool.scope(|scope| {
        //     for body in &mut ir_storage.generated_bodies {
        //         scope.spawn(|_| {
        //             optimiser.optimise(body);
        //         });
        //     }
        // });

        for body in bodies.iter_mut() {
            let optimiser = Optimiser::new(body_data, source_map, settings);
            optimiser.optimise(body);
        }

        Ok(())
    }

    fn cleanup(&mut self, _entry_point: SourceId, ctx: &mut Ctx) {
        let settings = ctx.settings().lowering_settings;
        let LoweringCtx { workspace, ir_storage, mut stdout, .. } = ctx.data();
        let source_map = &mut workspace.source_map;
        let bcx = &ir_storage.ctx;

        // we need to check if any of the bodies have been marked for `dumping`
        // and emit the IR that they have generated.
        if settings.dump_mode == IrDumpMode::Graph {
            graphviz::dump_ir_bodies(bcx, &ir_storage.bodies, settings.dump, &mut stdout).unwrap();
        } else {
            pretty::dump_ir_bodies(bcx, source_map, &ir_storage.bodies, settings.dump, &mut stdout)
                .unwrap();
        }
    }
}
