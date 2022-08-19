//! Hash AST semantic passes crate. This crate holds an implementation for the
//! visitor pattern on the AST to perform semantic checking and analysis on the
//! de-sugared AST.

#![feature(generic_associated_types)]

pub mod analysis;
pub(crate) mod diagnostics;
pub mod visitor;

use std::collections::HashSet;

use analysis::SemanticAnalyser;
use crossbeam_channel::unbounded;
use diagnostics::AnalysisDiagnostic;
use hash_ast::{ast::OwnsAstNode, visitor::AstVisitor};
use hash_pipeline::{sources::Workspace, traits::SemanticPass, CompilerResult};
use hash_reporting::report::Report;
use hash_source::SourceId;

pub struct HashSemanticAnalysis;

impl<'pool> SemanticPass<'pool> for HashSemanticAnalysis {
    /// A store representing modules that have already been analysed in the
    /// current pipeline.
    type State = HashSet<SourceId>;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(HashSet::default())
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
    fn perform_pass(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>> {
        let (sender, receiver) = unbounded::<AnalysisDiagnostic>();

        let source_map = &workspace.source_map;
        let node_map = &mut workspace.node_map;

        pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&entry_point) {
                if let SourceId::Interactive(id) = entry_point {
                    let source = node_map.get_interactive_block_mut(id);

                    // setup a visitor and the context
                    let mut visitor = SemanticAnalyser::new(source_map, entry_point);

                    visitor.visit_body_block(&(), source.node_ref()).unwrap();
                    visitor.send_generated_messages(&sender);
                }
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in node_map.iter_modules() {
                let source_id = SourceId::Module(*id);

                // Skip any modules that have already been de-sugared
                if state.contains(&source_id) {
                    continue;
                }

                let mut visitor = SemanticAnalyser::new(source_map, source_id);

                // Check that all of the root scope statements are only declarations
                let errors = visitor.visit_module(&(), module.node_ref()).unwrap();

                // We need to send the errors from the module too
                visitor.send_generated_messages(&sender);

                for (index, expr) in module.node().contents.iter().enumerate() {
                    // Skip any statements that we're deemed to be errors.
                    if errors.contains(&index) {
                        continue;
                    }

                    let sender = sender.clone();

                    scope.spawn(move |_| {
                        let mut visitor = SemanticAnalyser::new(source_map, source_id);

                        visitor.visit_expr(&(), expr.ast_ref()).unwrap();
                        visitor.send_generated_messages(&sender);
                    });
                }
            }
        });

        // Add all of the ids into the cache
        state.insert(entry_point);
        state.extend(workspace.node_map().iter_modules().map(|(id, _)| SourceId::Module(*id)));

        // Collect all of the errors
        drop(sender);
        let mut messages = receiver.into_iter().collect::<Vec<_>>();

        if messages.is_empty() {
            Ok(())
        } else {
            // We need to sort the reports by the source order so that the reports always
            // come out in a stable order.
            messages.sort_by_key(|item| item.id());

            Err(messages.into_iter().map(|item| item.into()).collect())
        }
    }
}
