//! Hash AST lowering passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to `lower` it to a simpler version so
//! that later stages can work on it without having to operate on similar
//! constructs and duplicating logic.

use hash_ast::{ast::OwnsAstNode, visitor::AstVisitorMut};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
    workspace::{SourceStageInfo, Workspace},
};
use hash_source::SourceId;
use hash_utils::rayon;
use visitor::AstDesugaring;

pub mod desugaring;
mod visitor;

/// The AST desugaring compiler stage. This will walk the AST, and
/// desugar all items within the [Workspace]. Desugaring is described
/// in more detail in [crate::desugaring].
pub struct AstDesugaringPass;

/// The [AstDesugaringCtx] represents all of the required information
/// that the [AstDesugaring] stage needs to query from the pipeline.
pub struct AstDesugaringCtx<'a> {
    /// Reference to the current compiler workspace.
    pub workspace: &'a mut Workspace,

    /// Reference to the rayon thread pool.
    pub pool: &'a rayon::ThreadPool,
}

pub trait AstDesugaringCtxQuery: CompilerInterface {
    fn data(&mut self) -> AstDesugaringCtx;
}

impl<Ctx: AstDesugaringCtxQuery> CompilerStage<Ctx> for AstDesugaringPass {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::DeSugar
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
    fn run(
        &mut self,
        entry_point: SourceId,
        ctx: &mut Ctx,
    ) -> hash_pipeline::interface::CompilerResult<()> {
        let AstDesugaringCtx { workspace, pool } = &mut ctx.data();

        let node_map = &mut workspace.node_map;
        let source_map = &workspace.source_map;
        let source_stage_info = &mut workspace.source_stage_info;

        pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !source_stage_info.get(entry_point).is_desugared() && entry_point.is_interactive() {
                let source = node_map.get_interactive_block_mut(entry_point.into());
                let mut desugarer = AstDesugaring::new(source_map);

                desugarer.visit_body_block(source.node_ref_mut()).unwrap();
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in node_map.iter_mut_modules().enumerate() {
                let source_id = SourceId::new_module(id as u32);
                let stage_info = source_stage_info.get(source_id);

                // Skip any modules that have already been de-sugared
                if stage_info.is_desugared() {
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
                    scope.spawn(move |_| {
                        let mut desugarer = AstDesugaring::new(source_map);
                        desugarer.visit_expr(expr.ast_ref_mut()).unwrap()
                    })
                }
            }
        });

        // Set all modules as ast-desugared
        source_stage_info.set_all(SourceStageInfo::DESUGARED);

        Ok(())
    }
}
