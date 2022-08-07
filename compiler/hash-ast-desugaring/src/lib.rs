//! Hash AST lowering passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to `lower` it to a simpler version so
//! that later stages can work on it without having to operate on similar
//! constructs and duplicating logic.
#![feature(generic_associated_types)]

use std::collections::HashSet;

use hash_ast::{ast::OwnsAstNode, visitor::AstVisitorMut};
use hash_pipeline::{sources::Workspace, traits::Desugar, CompilerResult};
use hash_source::SourceId;
use visitor::AstDesugaring;

pub mod desugaring;
mod visitor;

pub struct AstDesugarer;

impl<'pool> Desugar<'pool> for AstDesugarer {
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
    /// the "if-guard" pattern to express all of the branches in the
    /// if-statement.
    ///
    /// This function utilised the pipeline thread pool in order to make the
    /// transformations as parallel as possible. There is a queue that is
    /// queues all of the expressions within each [hash_ast::ast::Module].
    fn desugar(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        pool.scope(|scope| {
            let source_map = &workspace.source_map;
            let node_map = &mut workspace.node_map;

            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&entry_point) {
                if let SourceId::Interactive(id) = entry_point {
                    let source = node_map.get_interactive_block_mut(id);
                    let mut desugarer = AstDesugaring::new(source_map, entry_point);

                    desugarer.visit_body_block(&(), source.node_ref_mut()).unwrap();
                }
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in node_map.iter_mut_modules() {
                // Skip any modules that have already been de-sugared
                if state.contains(&SourceId::Module(*id)) {
                    continue;
                }

                // @@Future: So here, it would be nice that the de-sugaring visitor could have a
                // context that has access to the pool so that it could just push other jobs
                // into the queue rather than only splitting the job by top-level expressions.
                // This would work by the visitor pushing expressions into the work queue
                // whenever it hits body-blocks that have a list of expressions. This would
                // definitely make this process even faster, but it might add overhead to the
                // process of adding these items to the queue. However, it might be worth
                // investigating this in the future.
                for expr in module.node_mut().contents.iter_mut() {
                    scope.spawn(|_| {
                        let mut desugarer = AstDesugaring::new(source_map, SourceId::Module(*id));
                        desugarer.visit_expr(&(), expr.ast_ref_mut()).unwrap()
                    })
                }
            }
        });

        // Add all of the ids into the cache
        state.insert(entry_point);
        state.extend(workspace.node_map().iter_modules().map(|(id, _)| SourceId::Module(*id)));

        Ok(())
    }
}
