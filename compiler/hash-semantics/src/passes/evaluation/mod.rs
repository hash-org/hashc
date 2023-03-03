//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use derive_more::Constructor;
use hash_ast::ast::{self};
use hash_source::ModuleKind;
use hash_tir::{
    environment::env::AccessToEnv,
    fns::FnCallTerm,
    terms::TermId,
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_typecheck::AccessToTypechecking;

use super::ast_utils::AstPass;
use crate::{
    diagnostics::error::SemanticResult,
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
    fn find_and_construct_main_call(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> SemanticResult<Option<TermId>> {
        let source_id = self.current_source_info().source_id;
        let kind = self.source_map().module_kind_by_id(source_id);
        match kind {
            None | Some(ModuleKind::Normal | ModuleKind::Prelude) => Ok(None),
            Some(ModuleKind::EntryPoint) => {
                // Get the `main` function
                //
                // These should exist since the module kind was registered
                // as an entry point
                let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
                match self.mod_utils().get_mod_fn_member_by_ident(mod_def_id, "main") {
                    Some(fn_def_id) => {
                        let call_term = self.new_term(FnCallTerm {
                            subject: self.new_term(fn_def_id),
                            implicit: false,
                            args: self.new_empty_args(),
                        });

                        // Ensure it is well-typed
                        let (inferred_call_term, _) =
                            self.inference_ops().infer_term(call_term, self.new_ty_hole())?;

                        Ok(Some(inferred_call_term))
                    }
                    None => {
                        // @@Todo: This should be an error at some point,
                        // question is when.
                        Ok(None)
                    }
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
        println!("{}", self.env().with(result));

        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        let main_call_term = self.find_and_construct_main_call(node)?;

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
