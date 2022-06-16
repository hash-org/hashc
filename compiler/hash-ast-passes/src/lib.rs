//! Hash AST semantic passes crate. This crate holds an implementation for the
//! visitor pattern on the AST to perform semantic checking and analysis on the
//! de-sugared AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors
#![feature(generic_associated_types)]

mod error;
pub mod visitor;

use crossbeam_channel::unbounded;
use error::AnalysisError;
use hash_ast::visitor::AstVisitor;
use hash_pipeline::{sources::Sources, traits::SemanticPass, CompilerResult};
use hash_reporting::reporting::Report;
use hash_source::SourceId;
use std::collections::HashSet;
use visitor::{SemanticAnalyser, SemanticAnalysisContext};

impl<'pool> SemanticPass<'pool> for SemanticAnalyser {
    /// A store representing modules that have already been analysed in the current pipeline.
    type State = HashSet<SourceId>;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(HashSet::default())
    }

    /// This will perform a pass on the AST by checking the semantic rules that are within
    /// the language specification. The function will attempt to perform a pass on the
    /// `target` which happens on the main thread. The target may be either an interactive
    /// block or a module. A pass is performed and then remaining modules are processed if they
    /// have not already been processed. This is a sound implementation because it always considers
    /// the `target` which might not always occur within the modules map. Each time the pipeline
    /// runs (in the interactive case), the most recent block is always passed.
    fn perform_pass(
        &mut self,
        target: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>> {
        let (sender, receiver) = unbounded::<AnalysisError>();

        pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&target) {
                if let SourceId::Interactive(id) = target {
                    let source = sources.get_interactive_block_mut(id);

                    // setup a visitor and the context
                    let mut visitor = SemanticAnalyser::new();
                    let ctx = SemanticAnalysisContext::new(target);

                    visitor.visit_body_block(&ctx, source.node()).unwrap();
                    visitor
                        .errors()
                        .into_iter()
                        .for_each(|err| sender.send(err).unwrap());

                    // We have to add it here since we don't want it be re-passed further down
                    state.insert(target);
                }
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in sources.iter_modules() {
                // Skip any modules that have already been de-sugared
                if state.contains(&SourceId::Module(id)) {
                    continue;
                }

                for expr in module.node().contents.iter() {
                    let sender = sender.clone();

                    scope.spawn(move |_| {
                        let mut visitor = SemanticAnalyser::new();
                        let ctx = SemanticAnalysisContext::new(SourceId::Module(id));

                        visitor.visit_expression(&ctx, expr.ast_ref()).unwrap();
                        visitor
                            .errors()
                            .into_iter()
                            .for_each(|err| sender.send(err).unwrap());
                    });
                }
            }
        });

        // Add all of the ids into the cache
        state.extend(sources.iter_modules().map(|(id, _)| SourceId::Module(id)));

        // Collect all of the errors
        drop(sender);
        let errors = receiver.into_iter().collect::<Vec<_>>();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.into_iter().map(|err| err.into()).collect())
        }
    }
}
