//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![feature(decl_macro, let_chains)]

mod build;
mod cfg;
mod discover;

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

/// The Hash IR builder compiler stage. This will walk the AST, and
/// lower all items within a particular module.
pub struct AstLowerer;

impl AstLowerer {
    pub fn new() -> Self {
        Self
    }
}

impl Default for AstLowerer {
    fn default() -> Self {
        Self::new()
    }
}

pub trait IrLoweringCtx: CompilerInterface {
    fn data(&mut self) -> (&mut Workspace, &TyStorage, &mut IrStorage);
}

impl<Ctx: IrLoweringCtx> CompilerStage<Ctx> for AstLowerer {
    /// Return that this is [CompilerStageKind::IrGen].
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    /// Lower that AST of each module that is currently in the workspace
    /// into Hash IR. This will iterate over all modules, and possibly
    /// interactive statements to see if the need IR lowering, if so they
    /// are lowered and the result is saved on the [IrStorage].
    /// Additionally, this module is responsible for performing
    /// optimisations on the IR (if specified via the [CompilerSettings]).
    fn run_stage(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let settings = ctx.settings().lowering_settings;

        let (workspace, ty_storage, ir_storage) = ctx.data();
        let source_map = &mut workspace.source_map;
        let source_stage_info = &mut workspace.source_stage_info;

        let mut lowered_bodies = Vec::new();

        // We need to visit all of the modules in the workspace and discover
        // what needs to be lowered.
        for (module_id, module) in workspace.node_map.iter_modules() {
            let source_id = SourceId::Module(*module_id);
            let stage_info = source_stage_info.get(source_id);

            // Skip any modules that have already been checked
            if stage_info.is_lowered() {
                continue;
            }

            let mut discoverer = LoweringVisitor::new(
                &ty_storage.global,
                ir_storage,
                source_map,
                source_id,
                settings,
            );
            discoverer.visit_module(module.node_ref()).unwrap();

            // We need to add all of the bodies to the global bodies
            // store.
            lowered_bodies.extend(discoverer.into_bodies());
        }

        // we need to check if any of the bodies have been marked for `dumping`
        // and emit the IR that they have generated.

        if settings.dump_mode == IrDumpMode::Graph {
            graphviz::dump_ir_bodies(ir_storage, &lowered_bodies, settings.dump_all);
        } else {
            pretty::dump_ir_bodies(ir_storage, source_map, &lowered_bodies, settings.dump_all);
        }

        // Mark all modules now as lowered, and all generated
        // bodies to the store.
        source_stage_info.set_all(SourceStageInfo::LOWERED);
        ir_storage.add_bodies(lowered_bodies);

        Ok(())
    }
}
