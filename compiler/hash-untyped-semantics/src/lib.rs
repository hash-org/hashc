//! Hash AST semantic passes crate. This crate holds an implementation for the
//! visitor pattern on the AST to perform semantic checking and analysis on the
//! de-sugared AST.
#![feature(let_chains)]

pub mod analysis;
pub(crate) mod diagnostics;
pub mod visitor;

use analysis::SemanticAnalyser;
use crossbeam_channel::unbounded;
use diagnostics::AnalysisDiagnostic;
use hash_ast::{ast::OwnsAstNode, visitor::AstVisitorMutSelf};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::CompilerStageKind,
    workspace::{SourceStageInfo, Workspace},
};
use hash_reporting::reporter::Reports;
use hash_source::SourceId;

pub struct UntypedSemanticAnalysis;

/// The [SemanticAnalysisCtx] represents all of the required information
/// that the [SemanticAnalysis] stage needs to query from the pipeline.
pub struct UntypedSemanticAnalysisCtx<'s> {
    /// Reference to the current compiler workspace.
    pub workspace: &'s mut Workspace,

    /// Reference to the rayon thread pool.
    pub pool: &'s rayon::ThreadPool,
}

/// A trait that allows the [SemanticAnalysis] stage to query the
/// pipeline for the required information.
pub trait UntypedSemanticAnalysisCtxQuery: CompilerInterface {
    fn data(&mut self) -> UntypedSemanticAnalysisCtx;
}

impl<Ctx: UntypedSemanticAnalysisCtxQuery> CompilerStage<Ctx> for UntypedSemanticAnalysis {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::UntypedAnalysis
    }

    /// This will perform a pass on the AST by checking the semantic rules that
    /// are within the language specification. The function will attempt to
    /// perform a pass on the `entry_point` which happens on the main
    /// thread. The target may be either an interactive block or a module. A
    /// pass is performed and then remaining modules are processed if they
    /// have not already been processed. This is a sound implementation because
    /// it always considers the `entry_point` which might not always occur
    /// within the modules map. Each time the pipeline runs (in the
    /// interactive case), the most recent block is always passed.
    fn run(&mut self, entry_point: SourceId, stage_data: &mut Ctx) -> CompilerResult<()> {
        let (sender, receiver) = unbounded::<AnalysisDiagnostic>();
        let UntypedSemanticAnalysisCtx { workspace, pool } = stage_data.data();

        let source_map = &workspace.source_map;
        let node_map = &mut workspace.node_map;
        let source_stage_info = &mut workspace.source_stage_info;

        pool.scope(|scope| {
            if !source_stage_info.get(entry_point).is_semantics_checked()
                && entry_point.is_interactive()
            {
                let source = node_map.get_interactive_block(entry_point.into());

                // setup a visitor and the context
                let mut visitor = SemanticAnalyser::new(source_map);

                visitor.visit_body_block(source.node_ref()).unwrap();
                visitor.send_generated_messages(&sender);
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in node_map.iter_modules().enumerate() {
                let source_id = SourceId::new_module(id as u32);
                let stage_info = source_stage_info.get(source_id);

                // Skip any modules that have already been checked
                if stage_info.is_semantics_checked() {
                    continue;
                }

                let mut visitor = SemanticAnalyser::new(source_map);

                // Check that all of the root scope statements are only declarations
                let errors = visitor.visit_module(module.node_ref()).unwrap();

                // We need to send the errors from the module too
                visitor.send_generated_messages(&sender);

                for (index, expr) in module.node().contents.iter().enumerate() {
                    // Skip any statements that we're deemed to be errors.
                    if errors.contains(&index) {
                        continue;
                    }

                    let sender = sender.clone();

                    scope.spawn(move |_| {
                        let mut visitor = SemanticAnalyser::new(source_map);

                        visitor.visit_expr(expr.ast_ref()).unwrap();
                        visitor.send_generated_messages(&sender);
                    });
                }
            }
        });

        // Mark all modules now as semantically checked
        source_stage_info.set_all(SourceStageInfo::CHECKED_SEMANTICS);

        // Collect all of the errors
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
}
