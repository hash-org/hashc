//! Hash AST semantic passes crate. This crate holds an implementation for the
//! visitor pattern on the AST to perform semantic checking and analysis on the
//! de-sugared AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors
#![feature(generic_associated_types)]

mod error;
pub mod visitor;

use error::SemanticPassError;
use hash_ast::visitor::AstVisitor;
use hash_pipeline::{sources::Sources, traits::SemanticPass, CompilerResult};
use hash_reporting::reporting::Report;
use hash_source::SourceId;
use std::collections::HashSet;
use visitor::AstPasses;

impl<'pool> SemanticPass<'pool> for AstPasses {
    type State = HashSet<SourceId>;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(HashSet::default())
    }

    /// This function is used to lower all of the AST that is present within
    /// the modules to be compatible with the typechecking stage. This is
    /// essentially a pass that will transform the following structures
    /// into a "simpler" variant:
    ///
    /// Any for-loops are transformed into a more simpler "loop" construct
    /// with an inner match case that verifies that the iterator has no
    /// more items that can be consumed.
    ///
    /// Any while-loops are also transformed into a simpler loop variant with
    /// an inner match case that matches on the result of the while-loop
    /// "condition" to see if it is "true" or "false". If it is false, then
    /// the loop breaks, otherwise the body of the while-loop is executed.
    ///
    /// Any if-statements are transformed into equivalent match cases by using
    /// the "if-guard" pattern to express all of the branches in the if-statement.
    ///
    /// This function utilised the pipeline thread pool in order to make the transformations
    /// as parallel as possible. There is a queue that is queues all of the expressions within
    /// each [hash_ast::ast::Module].
    fn perform_pass(
        &mut self,
        target: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>> {
        let errors: Vec<SemanticPassError> = pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&target) {
                if let SourceId::Interactive(id) = target {
                    let source = sources.get_interactive_block_mut(id);

                    AstPasses.visit_body_block(&(), source.node()).unwrap()
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
                    scope.spawn(|_| AstPasses.visit_expression(&(), expr.ast_ref()).unwrap())
                }
            }

            vec![]
        });

        // Add all of the ids into the cache
        state.insert(target);
        state.extend(sources.iter_modules().map(|(id, _)| SourceId::Module(id)));

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.into_iter().map(|err| err.into()).collect())
        }
    }
}
