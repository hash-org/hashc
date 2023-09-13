//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use hash_ast::ast::{self};
use hash_pipeline::settings::CompilerStageKind;
use hash_source::{ModuleKind, SourceId};
use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{
    args::Arg,
    dump::dump_tir,
    fns::CallTerm,
    node::{Node, NodeId},
    terms::{Term, TermId},
};
use hash_typecheck::{normalisation::NormalisationMode, TcEnv};
use hash_utils::{
    derive_more::{Constructor, Deref},
    stream_less_writeln,
};

use super::{analysis_pass::AnalysisPass, ast_info::AstInfo};
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
    passes::tc_env_impl::TcEnvImpl,
    progress::AnalysisStage,
};

/// The potential fourth pass of analysis, which executes and dumps the TIR, if
/// the correct compiler flags are set.
#[derive(Constructor, Deref)]
pub struct EvaluationPass<'env, E: SemanticEnv> {
    #[deref]
    env: &'env E,
    ast_info: &'env AstInfo,
}

impl<E: SemanticEnv> EvaluationPass<'_, E> {
    /// Find and construct a term that calls the `main` function, if we are in
    /// an entry point module.
    fn find_and_construct_main_call(&self, source: SourceId) -> SemanticResult<Option<TermId>> {
        let kind = source.module_kind();
        match kind {
            None | Some(ModuleKind::Normal | ModuleKind::Prelude) => Ok(None),
            Some(ModuleKind::EntryPoint) => {
                // Get the `main` function or custom entry point
                //
                // This should exist since the module kind was registered
                // as an entry point during inference.
                let def = self.entry_point().def();
                match def {
                    Some(def) => {
                        let call_term = Term::from(
                            CallTerm {
                                subject: Term::from(def, def.origin()),
                                implicit: false,
                                args: Node::create_at(Node::<Arg>::empty_seq(), def.origin()),
                            },
                            def.origin(),
                        );
                        Ok(Some(call_term))
                    }
                    None => {
                        // We only care about this error if we're running to
                        // the evaluation stage, or if
                        // we are continuing after lowering
                        let settings = self.compiler_settings();
                        if settings.stage > CompilerStageKind::Lower
                            || settings.semantic_settings.eval_tir
                        {
                            Err(SemanticError::EntryPointNotFound)
                        } else {
                            Ok(None)
                        }
                    }
                }
            }
        }
    }
}

impl<E: SemanticEnv> AnalysisPass for EvaluationPass<'_, E> {
    type Env = E;
    fn env(&self) -> &Self::Env {
        self.env
    }

    type PassOutput = ();
    fn pass_interactive(
        &self,
        source: SourceId,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::diagnostics::definitions::SemanticResult<()> {
        let tc = TcEnvImpl::new(self.env, source);
        let term = self.ast_info.terms().get_data_by_node(node.id()).unwrap();

        // Potentially dump the TIR and evaluate it depending on flags.
        if self.compiler_settings().semantic_settings.dump_tir {
            dump_tir(term);
        }

        // Interactive mode is always evaluated.
        let result = tc.norm_ops().with_mode(NormalisationMode::Full).normalise(term.into())?;
        stream_less_writeln!("{}", result);

        Ok(())
    }

    fn pass_module(
        &self,
        source: SourceId,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::definitions::SemanticResult<()> {
        let tc = TcEnvImpl::new(self.env, source);
        let mod_def_id = self.ast_info.mod_defs().get_data_by_node(node.id()).unwrap();
        let main_call_term = self.find_and_construct_main_call(source)?;

        // Potentially dump the TIR and evaluate it depending on flags.
        let settings = self.compiler_settings().semantic_settings();

        if settings.dump_tir {
            dump_tir(mod_def_id);
        }

        if settings.eval_tir {
            if let Some(term) = main_call_term {
                let _ = tc.norm_ops().with_mode(NormalisationMode::Full).normalise(term.into())?;
            }
        }

        Ok(())
    }

    fn pre_pass(&self, source: SourceId) -> SemanticResult<Option<()>> {
        if self.get_current_progress(source) == AnalysisStage::BodyInference {
            self.set_current_progress(source, AnalysisStage::PreEvaluation);
            Ok(None)
        } else {
            Ok(Some(()))
        }
    }
}
