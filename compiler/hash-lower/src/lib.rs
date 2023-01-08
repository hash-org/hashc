//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![feature(decl_macro, let_chains)]

mod build;
mod cfg;
mod discover;
mod optimise;

use discover::LoweringVisitor;
use hash_ast::ast::{AstVisitorMutSelf, OwnsAstNode};
use hash_ir::{
    write::{graphviz, pretty},
    IrStorage,
};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::{CompilerStageKind, IrDumpMode},
    workspace::{SourceStageInfo, Workspace},
};
use hash_source::SourceId;
use hash_types::storage::TyStorage;
use optimise::Optimiser;

/// The Hash IR builder compiler stage. This will walk the AST, and
/// lower all items within a particular module.
#[derive(Default)]
pub struct IrGen;

/// The [LoweringCtx] represents all of the required information
/// that the [AstLowerer] stage needs to query from the pipeline
/// in order to perform its lowering operations.
pub struct LoweringCtx<'ir> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ir mut Workspace,

    /// Reference to the type storage that comes from
    /// the typechecking compiler phase.
    pub ty_storage: &'ir TyStorage,

    /// Reference to the IR storage that is used to store
    /// the lowered IR, and all metadata about the IR.
    pub ir_storage: &'ir mut IrStorage,

    /// Reference to the rayon thread pool.
    pub _pool: &'ir rayon::ThreadPool,
}

pub trait LoweringCtxQuery: CompilerInterface {
    fn data(&mut self) -> LoweringCtx<'_>;
}

impl<Ctx: LoweringCtxQuery> CompilerStage<Ctx> for IrGen {
    /// Return that this is [CompilerStageKind::IrGen].
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    /// Lower that AST of each module that is currently in the workspace
    /// into Hash IR. This will iterate over all modules, and possibly
    /// interactive statements to see if the need IR lowering, if so they
    /// are lowered and the result is saved on the [IrStorage].
    /// Additionally, this module is responsible for performing
    /// optimisations on the IR (if specified via the [CompilerSettings]).
    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let settings = ctx.settings().lowering_settings;

        let LoweringCtx { workspace, ty_storage, ir_storage, .. } = ctx.data();
        let source_map = &mut workspace.source_map;
        let source_stage_info = &mut workspace.source_stage_info;

        let mut lowered_bodies = Vec::new();

        // We need to visit all of the modules in the workspace and discover
        // what needs to be lowered.
        for (id, module) in workspace.node_map.iter_modules().enumerate() {
            let source_id = SourceId::new_module(id as u32);
            let stage_info = source_stage_info.get(source_id);

            // Skip any modules that have already been checked
            if stage_info.is_lowered() {
                continue;
            }

            let mut discoverer = LoweringVisitor::new(
                &ty_storage.global,
                &mut ir_storage.ctx,
                source_map,
                source_id,
                settings,
            );
            discoverer.visit_module(module.node_ref()).unwrap();

            // We need to add all of the bodies to the global bodies
            // store.
            lowered_bodies.extend(discoverer.into_bodies());
        }

        // Mark all modules now as lowered, and all generated
        // bodies to the store.
        source_stage_info.set_all(SourceStageInfo::LOWERED);
        ir_storage.add_bodies(lowered_bodies);

        Ok(())
    }
}

/// Compiler stage that is responsible for performing optimisations on the
/// Hash IR. This will iterate over all of the bodies that have been generated
/// and perform optimisations on them based on if they are applicable and the
/// current configuration settings of the compiler.
#[derive(Default)]
pub struct IrOptimiser;

impl<Ctx: LoweringCtxQuery> CompilerStage<Ctx> for IrOptimiser {
    /// Return that this is [CompilerStageKind::IrGen].
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let settings = ctx.settings().lowering_settings;

        let LoweringCtx { workspace, ir_storage, .. } = ctx.data();
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
        let LoweringCtx { workspace, ir_storage, .. } = ctx.data();
        let source_map = &mut workspace.source_map;
        let bcx = &ir_storage.ctx;

        // we need to check if any of the bodies have been marked for `dumping`
        // and emit the IR that they have generated.
        if settings.dump_mode == IrDumpMode::Graph {
            graphviz::dump_ir_bodies(bcx, &ir_storage.bodies, settings.dump_all);
        } else {
            pretty::dump_ir_bodies(bcx, source_map, &ir_storage.bodies, settings.dump_all);
        }
    }
}
