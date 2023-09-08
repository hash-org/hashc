//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use hash_ast::ast;
use hash_reporting::diagnostic::AccessToDiagnostics;
use hash_tir::{terms::Ty, utils::traversing::Atom};
use hash_typecheck::{
    errors::{TcError, TcResult},
    inference::FnInferMode,
    AccessToTypechecking,
};
use hash_utils::derive_more::Constructor;

use super::ast_utils::AstPass;
use crate::{
    diagnostics::error::SemanticResult,
    environment::{
        analysis_progress::AnalysisStage,
        sem_env::{AccessToSemEnv, SemEnv},
    },
    impl_access_to_sem_env,
    ops::common::CommonOps,
};

/// The third pass of the typechecker, which infers all remaining terms and
/// types.
#[derive(Constructor)]
pub struct InferencePass<'tc> {
    sem_env: &'tc SemEnv<'tc>,
}

impl_access_to_sem_env!(InferencePass<'_>);

impl InferencePass<'_> {
    /// Infer the given subject by the provided closure, or error if it contains
    /// holes.
    fn infer_fully<T: Copy>(
        &self,
        orig_subject: T,
        infer_subject: impl Fn(T) -> TcResult<T>,
        subject_has_holes: impl Fn(T) -> Option<Atom>,
    ) -> TcResult<T> {
        let subject = self.try_or_add_error(try { infer_subject(orig_subject)? });

        // If we have an error, in diagnostics mode, exit.
        if self.has_errors() {
            return Err(TcError::Signal);
        }

        // If we have holes, error
        if let Some(subject) = subject && let Some(hole) = subject_has_holes(subject)
            && self.get_current_progress() == AnalysisStage::BodyInference
        {
            self.add_error(self.convert_tc_error(TcError::NeedMoreTypeAnnotationsToInfer {
                atom: hole,
            }));
        }

        Ok(subject.unwrap_or(orig_subject))
    }
}

impl<'tc> AstPass for InferencePass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        // Infer the expression
        let term = self.ast_info().terms().get_data_by_node(node.id()).unwrap();
        let (term, _) = self.infer_fully(
            (term, Ty::hole_for(term)),
            |(term_id, ty_id)| {
                self.infer_ops().infer_term(term_id, ty_id)?;
                Ok((term_id, ty_id))
            },
            |(term_id, ty_id)| {
                self.sub_ops().atom_has_holes(term_id).or(self.sub_ops().atom_has_holes(ty_id))
            },
        )?;
        self.ast_info().terms().insert(node.id(), term);
        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        // Infer the whole module
        let _ = self.infer_fully(
            self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap(),
            |mod_def_id| {
                self.infer_ops().infer_mod_def(
                    mod_def_id,
                    match self.get_current_progress() {
                        AnalysisStage::HeaderInference => FnInferMode::Header,
                        AnalysisStage::BodyInference => FnInferMode::Body,
                        _ => unreachable!(),
                    },
                )?;
                Ok(mod_def_id)
            },
            |mod_def_id| self.sub_ops().mod_def_has_holes(mod_def_id),
        )?;
        // Mod def is already registered in the ast info
        Ok(())
    }

    fn pre_pass(&self) -> SemanticResult<bool> {
        if self.get_current_progress() == AnalysisStage::Resolution {
            self.set_current_progress(AnalysisStage::HeaderInference);
            Ok(true)
        } else if self.get_current_progress() == AnalysisStage::HeaderInference {
            self.set_current_progress(AnalysisStage::BodyInference);
            Ok(true)
        } else {
            Ok(false)
        }
    }
}
