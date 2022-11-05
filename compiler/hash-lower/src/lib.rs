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
use hash_ir::{write::IrWriter, IrStorage};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::CompilerStageKind,
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
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    fn run_stage(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
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

            let mut discoverer =
                LoweringVisitor::new(&ty_storage.global, ir_storage, source_map, source_id);
            discoverer.visit_module(module.node_ref()).unwrap();

            // We need to add all of the bodies to the global bodies
            // store.
            lowered_bodies.extend(discoverer.into_bodies());
        }

        // we need to check if any of the bodies have been marked for `dumping`
        // and emit the IR that they have generated.
        let bodies_to_dump = lowered_bodies
            .iter()
            .enumerate()
            .filter(|(_, body)| body.needs_dumping())
            .map(|(index, _)| index)
            .collect::<Vec<_>>();

        for (index, body_index) in bodies_to_dump.into_iter().enumerate() {
            // Use a newline as a separator between each body
            if index > 0 {
                println!();
            }

            let body = &lowered_bodies[body_index];
            println!(
                "IR dump for {} `{}` defined at {}\n{}",
                body.source(),
                body.name(),
                source_map.fmt_location(body.location()),
                IrWriter::new(ir_storage, body)
            );
        }

        // Mark all modules now as lowered, and all generated
        // bodies to the store.
        source_stage_info.set_all(SourceStageInfo::LOWERED);
        ir_storage.add_bodies(lowered_bodies);

        Ok(())
    }
}
