//! Hash AST expanding passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to expand any directives or macros that
//! need to run after the parsing stage. Currently this function does not have

use hash_ast::ast::{AstVisitorMutSelf, OwnsAstNode};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerOutputStream, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::{SourceStageInfo, Workspace},
};
use hash_source::SourceId;
use visitor::AstExpander;

mod diagnostics;
mod visitor;

/// The [AstExpansionPass] represents the stage in the pipeline that will
/// expand any macros or directives that are present within the AST.
///
/// Currently, this stage doesn't have a big role to play within compilation,
/// but once there is a more formal specification of directives, and a macro
/// system, then this stage will be the center of that.
pub struct AstExpansionPass;

/// The [AstExpansionCtx] represents all of the required information
/// that the [AstExpansionPass] stage needs to query from the pipeline.
pub struct AstExpansionCtx<'ast> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ast mut Workspace,

    /// Settings to the compiler
    pub settings: &'ast CompilerSettings,

    /// Reference to the output stream
    pub stdout: CompilerOutputStream,
}

/// A trait that allows the [AstExpansionPass] stage to query the
/// pipeline for the required information.
pub trait AstExpansionCtxQuery: CompilerInterface {
    fn data(&mut self) -> AstExpansionCtx;
}

impl<Ctx: AstExpansionCtxQuery> CompilerStage<Ctx> for AstExpansionPass {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Expand
    }

    /// This will perform a pass on the AST by expanding any macros or
    /// directives that are present within the AST. Currently, this
    /// stage deals with `#dump_ast` directives to dump AST after it
    /// has been generated, and de-sugared.
    fn run(
        &mut self,
        entry_point: SourceId,
        ctx: &mut Ctx,
    ) -> hash_pipeline::interface::CompilerResult<()> {
        let AstExpansionCtx { workspace, stdout, settings } = ctx.data();

        let node_map = &mut workspace.node_map;
        let source_map = &workspace.source_map;
        let source_stage_info = &mut workspace.source_stage_info;

        let source_info = source_stage_info.get(entry_point);

        // De-sugar the target if it isn't already de-sugared
        if source_info.is_expanded() && entry_point.is_interactive() {
            let mut expander = AstExpander::new(source_map, settings, stdout.clone());
            let source = node_map.get_interactive_block(entry_point.into());

            expander.visit_body_block(source.node_ref()).unwrap();
        }

        for (id, module) in node_map.iter_modules().enumerate() {
            let source_id = SourceId::new_module(id as u32);
            let stage_info = source_stage_info.get(source_id);

            // Skip any modules that have already been de-sugared
            if stage_info.is_expanded() {
                continue;
            }

            let mut expander = AstExpander::new(source_map, settings, stdout.clone());
            expander.visit_module(module.node_ref()).unwrap();
        }

        // Update all entries that they have been expanded
        source_stage_info.set_all(SourceStageInfo::EXPANDED);

        Ok(())
    }

    /// Check whether the compiler settings specify that the generated
    /// AST needs to be dumped.
    fn cleanup(&mut self, entry_point: SourceId, ctx: &mut Ctx) {
        let settings = ctx.settings();
        let mut stdout = ctx.output_stream();

        if settings.stage > CompilerStageKind::Parse && settings.ast_settings().dump {
            ctx.workspace().print_sources(entry_point, &mut stdout, settings).unwrap();
        }
    }
}
