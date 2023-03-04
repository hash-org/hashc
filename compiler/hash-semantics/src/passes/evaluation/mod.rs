//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use derive_more::Constructor;
use hash_ast::ast::{self};
use hash_source::ModuleKind;
use hash_tir::{
    environment::env::AccessToEnv, fns::FnCallTerm, terms::TermId, utils::common::CommonUtils,
};
use hash_typecheck::AccessToTypechecking;
use hash_utils::stream_less_writeln;

use super::ast_utils::AstPass;
use crate::{
    diagnostics::error::{SemanticError, SemanticResult},
    environment::sem_env::{AccessToSemEnv, SemEnv},
    impl_access_to_sem_env,
};

/// The potential fourth pass of analysis, which executes and dumps the TIR, if
/// the correct compiler flags are set.
#[derive(Constructor)]
pub struct EvaluationPass<'tc> {
    sem_env: &'tc SemEnv<'tc>,
}

impl_access_to_sem_env!(EvaluationPass<'_>);

impl EvaluationPass<'_> {
    /// Find the main module definition, if it exists.
    fn find_and_construct_main_call(&self) -> SemanticResult<Option<TermId>> {
        let source_id = self.current_source_info().source_id;
        let kind = self.source_map().module_kind_by_id(source_id);
        match kind {
            None | Some(ModuleKind::Normal | ModuleKind::Prelude) => Ok(None),
            Some(ModuleKind::EntryPoint) => {
                // Get the `main` function or custom entry point
                //
                // This should exist since the module kind was registered
                // as an entry point during inference.
                let def = AccessToSemEnv::entry_point(self).def();
                match def {
                    Some(def) => {
                        let call_term = self.new_term(FnCallTerm {
                            subject: self.new_term(def),
                            implicit: false,
                            args: self.new_empty_args(),
                        });
                        Ok(Some(call_term))
                    }
                    None => Err(SemanticError::EntryPointNotFound),
                }
            }
        }
    }
}

impl<'tc> AstPass for EvaluationPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        let term = self.ast_info().terms().get_data_by_node(node.id()).unwrap();

        // Potentially dump the TIR and evaluate it depending on flags.
        if self.flags().dump_tir {
            self.dump_tir(self.env().with(term));
        }

        // Interactive mode is always evaluated.
        let result = self.normalisation_ops().normalise(term.into())?;
        stream_less_writeln!("{}", self.env().with(result));

        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        let main_call_term = self.find_and_construct_main_call()?;

        // Potentially dump the TIR and evaluate it depending on flags.
        //
        if self.flags().dump_tir {
            self.dump_tir(self.env().with(mod_def_id));
        }

        if self.flags().eval_tir {
            if let Some(term) = main_call_term {
                let _ = self.normalisation_ops().normalise(term.into())?;
            }
        }

        Ok(())
    }
}
