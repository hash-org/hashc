//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.

use hash_pipeline::traits::Lowering;

mod builder;

pub struct IrLowerer;

impl<'c> Lowering<'c> for IrLowerer {
    type State = ();

    fn make_state(&mut self) -> hash_pipeline::traits::CompilerResult<Self::State> {
        Ok(())
    }

    fn lower_interactive_block<'pool>(
        &'pool mut self,
        _interactive_id: hash_source::InteractiveId,
        _workspace: &hash_pipeline::sources::Workspace,
        _state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        todo!()
    }

    fn lower_module(
        &mut self,
        _module_id: hash_source::ModuleId,
        _workspace: &hash_pipeline::sources::Workspace,
        _state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        todo!()
    }
}
