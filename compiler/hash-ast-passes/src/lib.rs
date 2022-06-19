//! Hash AST semantic passes crate. This crate holds an implementation for the
//! visitor pattern on the AST to perform semantic checking and analysis on the
//! de-sugared AST.

#![feature(generic_associated_types)]

pub mod analysis;
pub(crate) mod diagnostics;
pub mod visitor;

use analysis::SemanticAnalyser;
use crossbeam_channel::unbounded;

use diagnostics::Diagnostic;
use hash_ast::visitor::AstVisitor;
use hash_pipeline::{sources::Sources, traits::SemanticPass, CompilerResult};
use hash_reporting::reporting::Report;
use hash_source::SourceId;
use std::collections::HashSet;

pub struct HashSemanticAnalysis;

impl<'pool> SemanticPass<'pool> for HashSemanticAnalysis {
    /// A store representing modules that have already been analysed in the current pipeline.
    type State = HashSet<SourceId>;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(HashSet::default())
    }

    /// This will perform a pass on the AST by checking the semantic rules that are within
    /// the language specification. The function will attempt to perform a pass on the
    /// `entry_point` which happens on the main thread. The target may be either an interactive
    /// block or a module. A pass is performed and then remaining modules are processed if they
    /// have not already been processed. This is a sound implementation because it always considers
    /// the `entry_point` which might not always occur within the modules map. Each time the pipeline
    /// runs (in the interactive case), the most recent block is always passed.
    fn perform_pass(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>> {
        let (sender, receiver) = unbounded::<Diagnostic>();

        pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&entry_point) {
                if let SourceId::Interactive(id) = entry_point {
                    let source = sources.get_interactive_block_mut(id);

                    // setup a visitor and the context
                    let mut visitor = SemanticAnalyser::new(entry_point);

                    visitor.visit_body_block(&(), source.node()).unwrap();
                    visitor.send_generated_messages(&sender);
                }
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in sources.iter_modules() {
                // Skip any modules that have already been de-sugared
                if state.contains(&SourceId::Module(id)) {
                    continue;
                }

                let mut visitor = SemanticAnalyser::new(SourceId::Module(id));

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
                        let mut visitor = SemanticAnalyser::new(SourceId::Module(id));

                        visitor.visit_expression(&(), expr.ast_ref()).unwrap();
                        visitor.send_generated_messages(&sender);
                    });
                }
            }
        });

        // Add all of the ids into the cache
        state.insert(entry_point);
        state.extend(sources.iter_modules().map(|(id, _)| SourceId::Module(id)));

        // Collect all of the errors
        drop(sender);
        let messages = receiver.into_iter().collect::<Vec<_>>();

        if messages.is_empty() {
            Ok(())
        } else {
            Err(messages.into_iter().map(|message| message.into()).collect())
        }
    }
}
