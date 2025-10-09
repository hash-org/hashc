//! Hash AST expanding passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to expand any directives or macros that
//! need to run after the parsing stage. Currently this function does not have

use diagnostics::ExpansionDiagnostic;
use expander::AstExpander;
use hash_ast::ast::{AstVisitorMutSelf, OwnsAstNode};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::{SourceStageInfo, Workspace},
};
use hash_reporting::reporter::Reports;
use hash_source::SourceId;
use hash_target::data_layout::TargetDataLayout;
use hash_utils::{crossbeam_channel::unbounded, rayon};

mod attr;
mod diagnostics;
mod expander;

/// The [AstExpansionPass] represents the stage in the pipeline that will
/// expand any macros or directives that are present within the AST.
///
/// Currently, this stage doesn't have a big role to play within compilation,
/// but once there is a more formal specification of directives, and a macro
/// system, then this stage will be the center of that.
pub struct AstExpansionPass;

/// The [AstExpansionCtx] represents all of the required information
/// that the [AstExpansionPass] stage needs to query from the pipeline.
pub struct AstExpansionCtx<'ctx> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ctx mut Workspace,

    /// Settings to the compiler
    pub settings: &'ctx CompilerSettings,

    /// Information about the current target data layout.
    pub data_layout: &'ctx TargetDataLayout,

    /// The thread pool.
    pub pool: &'ctx rayon::ThreadPool,
}

/// A trait that allows the [AstExpansionPass] stage to query the
/// pipeline for the required information.
pub trait AstExpansionCtxQuery: CompilerInterface {
    fn data(&mut self) -> AstExpansionCtx<'_>;
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
        let AstExpansionCtx { workspace, data_layout, settings, pool } = ctx.data();
        let (sender, receiver) = unbounded::<ExpansionDiagnostic>();

        let node_map = &mut workspace.node_map;
        let source_stage_info = &mut workspace.source_stage_info;

        let make_expander = |source| AstExpander::new(source, settings, data_layout);

        pool.scope(|scope| {
            let source_info = source_stage_info.get(entry_point);

            // De-sugar the target if it isn't already de-sugared
            if source_info.is_expanded() && entry_point.is_interactive() {
                let mut expander = make_expander(entry_point);
                let source = node_map.get_interactive_block(entry_point.into());

                expander.visit_body_block(source.node_ref()).unwrap();
                expander.emit_diagnostics_to(&sender);
            }

            for (id, module) in node_map.iter_modules() {
                let source_id = SourceId::from(*id);
                let stage_info = source_stage_info.get(source_id);

                // Skip any modules that have already been de-sugared
                if stage_info.is_expanded() {
                    continue;
                }

                // Check the module for any module-level invocations.
                let mut expander = make_expander(source_id);
                expander.visit_module(module.node().ast_ref()).unwrap();
                expander.emit_diagnostics_to(&sender);

                // Then queue up all of the expressions in the module for expansion.
                for expr in module.node().contents.iter() {
                    let sender = sender.clone();
                    scope.spawn(move |_| {
                        let mut expander = make_expander(source_id);
                        expander.visit_expr(expr.ast_ref()).unwrap();
                        expander.emit_diagnostics_to(&sender);
                    });
                }
            }
        });

        // Update all entries that they have been expanded
        source_stage_info.set_all(SourceStageInfo::EXPANDED);

        drop(sender);
        let mut messages = receiver.into_iter().collect::<Vec<_>>();

        if messages.is_empty() {
            Ok(())
        } else {
            // We need to sort the reports by the source order so that the reports always
            // come out in a stable order.
            messages.sort_by_key(|item| item.id());
            Err(messages.into_iter().flat_map(Reports::from).collect())
        }
    }

    /// Check whether the compiler settings specify that the generated
    /// AST needs to be dumped.
    fn cleanup(&mut self, _: SourceId, ctx: &mut Ctx) {
        let settings = ctx.settings();

        if settings.stage > CompilerStageKind::Parse && settings.ast_settings().dump {
            let set = settings.character_set;
            let mode = settings.ast_settings.dump_mode;
            ctx.workspace().print_sources(mode, set);
        }
    }
}
