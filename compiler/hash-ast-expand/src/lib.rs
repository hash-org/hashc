//! Hash AST expanding passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to expand any directives or macros that
//! need to run after the parsing stage. Currently this function does not have

use hash_ast::ast::{AstVisitor, OwnsAstNode};
use hash_pipeline::{settings::CompilerStageKind, sources::Workspace, traits::CompilerStage};
use hash_source::SourceId;
use visitor::AstExpander;

mod visitor;

pub struct AstExpansionPass;

impl<'pool> CompilerStage<'pool> for AstExpansionPass {
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::DeSugar
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        _: &'pool rayon::ThreadPool,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        let desugared_modules = &mut workspace.desugared_modules;
        let node_map = &mut workspace.node_map;

        // De-sugar the target if it isn't already de-sugared
        if !desugared_modules.contains(&entry_point) {
            if let SourceId::Interactive(id) = entry_point {
                let expander = AstExpander::new(&workspace.source_map, entry_point);
                let source = node_map.get_interactive_block(id);

                expander.visit_body_block(source.node_ref()).unwrap();
            }
        }

        for (id, module) in node_map.iter_modules() {
            let module_id = SourceId::Module(*id);

            // Skip any modules that have already been de-sugared
            if desugared_modules.contains(&module_id) {
                continue;
            }

            let expander = AstExpander::new(&workspace.source_map, module_id);
            expander.visit_module(module.node_ref()).unwrap();
        }

        Ok(())
    }
}
