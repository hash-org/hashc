//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use hash_ast::ast;
use hash_source::SourceId;
use hash_tir::{context::Context, tir::Ty, visitor::Atom};
use hash_typecheck::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    tc::FnInferMode,
    traits::OperationsOnNode,
};
use hash_utils::derive_more::{Constructor, Deref};

use super::{analysis_pass::AnalysisPass, ast_info::AstInfo, tc_env_impl::TcEnvImpl};
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv, progress::AnalysisStage};

/// The third pass of the typechecker, which infers all remaining terms and
/// types.
#[derive(Constructor, Deref)]
pub struct InferencePass<'env, E: SemanticEnv> {
    #[deref]
    env: &'env E,
    ast_info: &'env AstInfo,
}

impl<E: SemanticEnv> InferencePass<'_, E> {
    /// Infer the given subject by the provided closure, or error if it contains
    /// holes.
    fn infer_fully<T: Copy>(
        &self,
        source: SourceId,
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
            && self.get_current_progress(source) == AnalysisStage::BodyInference
        {
            self.add_error(TcError::NeedMoreTypeAnnotationsToInfer {
                atom: hole,
            }.into());
        }

        Ok(subject.unwrap_or(orig_subject))
    }
}

impl<E: SemanticEnv> AnalysisPass for InferencePass<'_, E> {
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
        let env = TcEnvImpl::new(self.env, source);
        let context = Context::new();
        let tc = env.checker(&context);
        tc.fn_infer_mode.set(FnInferMode::Body);

        // Infer the expression
        let term = self.ast_info.terms().get_data_by_node(node.id()).unwrap();
        let (term, _) = self.infer_fully(
            source,
            (term, Ty::hole_for(term)),
            |(term_id, ty_id)| {
                tc.check_node(term_id, ty_id)?;
                Ok((term_id, ty_id))
            },
            |(term_id, ty_id)| {
                tc.substituter().has_holes(term_id).or(tc.substituter().has_holes(ty_id))
            },
        )?;
        self.ast_info.terms().insert(node.id(), term);
        Ok(())
    }

    fn pass_module(
        &self,
        source: SourceId,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::definitions::SemanticResult<()> {
        let env = TcEnvImpl::new(self.env, source);
        let context = Context::new();
        let tc = env.checker(&context);
        tc.fn_infer_mode.set(match self.get_current_progress(source) {
            AnalysisStage::HeaderInference => FnInferMode::Header,
            AnalysisStage::BodyInference => FnInferMode::Body,
            _ => unreachable!(),
        });

        // Infer the whole module
        let _ = self.infer_fully(
            source,
            self.ast_info.mod_defs().get_data_by_node(node.id()).unwrap(),
            |mod_def_id| {
                tc.check_node(mod_def_id, ())?;
                Ok(mod_def_id)
            },
            |mod_def_id| tc.substituter().has_holes(mod_def_id),
        )?;
        // Mod def is already registered in the ast info
        Ok(())
    }

    fn pre_pass(&self, source: SourceId) -> SemanticResult<Option<()>> {
        if self.get_current_progress(source) == AnalysisStage::Resolution {
            self.set_current_progress(source, AnalysisStage::HeaderInference);
            Ok(None)
        } else if self.get_current_progress(source) == AnalysisStage::HeaderInference {
            self.set_current_progress(source, AnalysisStage::BodyInference);
            Ok(None)
        } else {
            Ok(Some(()))
        }
    }
}
