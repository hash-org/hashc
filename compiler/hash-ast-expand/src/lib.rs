//! Hash AST expanding passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to expand any directives or macros that
//! need to run after the parsing stage. Currently this function does not have

use hash_ast::ast::{AstVisitor, OwnsAstNode};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
    workspace::{SourceStageInfo, Workspace},
};
use hash_source::SourceId;
use visitor::AstExpander;

mod visitor;

pub struct AstExpansionPass;

pub trait AstExpansionCtx: CompilerInterface {
    fn data(&mut self) -> &mut Workspace;
}

impl<Ctx: AstExpansionCtx> CompilerStage<Ctx> for AstExpansionPass {
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::DeSugar
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        ctx: &mut Ctx,
    ) -> hash_pipeline::interface::CompilerResult<()> {
        let workspace = ctx.data();

        let node_map = &mut workspace.node_map;
        let source_map = &workspace.source_map;
        let source_stage_info = &mut workspace.source_stage_info;

        let source_info = source_stage_info.get(entry_point);

        // De-sugar the target if it isn't already de-sugared
        if source_info.is_expanded() {
            if let SourceId::Interactive(id) = entry_point {
                let expander = AstExpander::new(source_map, entry_point);
                let source = node_map.get_interactive_block(id);

                expander.visit_body_block(source.node_ref()).unwrap();
            }
        }

        for (id, module) in node_map.iter_modules() {
            let module_id = SourceId::Module(*id);
            let stage_info = source_stage_info.get(module_id);

            // Skip any modules that have already been de-sugared
            if stage_info.is_expanded() {
                continue;
            }

            let expander = AstExpander::new(source_map, module_id);
            expander.visit_module(module.node_ref()).unwrap();
        }

        // Update all entries that they have been expanded
        source_stage_info.set_all(SourceStageInfo::EXPANDED);

        Ok(())
    }
}
