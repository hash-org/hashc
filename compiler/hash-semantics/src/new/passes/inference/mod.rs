//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use derive_more::Constructor;
use hash_ast::ast::{self};
use hash_tir::new::{environment::env::AccessToEnv, utils::common::CommonUtils};
use hash_typecheck::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};
use hash_utils::stream_less_writeln;

use super::ast_utils::AstPass;
use crate::{
    impl_access_to_tc_env,
    new::environment::tc_env::{AccessToTcEnv, TcEnv},
};

/// The third pass of the typechecker, which infers all remaining terms and
/// types.
#[derive(Constructor)]
pub struct InferencePass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(InferencePass<'_>);

/// The maximum number of hole-filling iterations to perform when inferring a
/// term, before giving up and reporting an error.
const MAX_INFER_ITERATIONS: usize = 2;

impl InferencePass<'_> {
    /// Infer the given subject by the provided closure, until it contains no
    /// more holes.
    ///
    /// If `MAX_INFER_ITERATIONS` is reached, then an error is returned.
    fn infer_loop<T: Copy>(
        &self,
        subject: T,
        infer_subject: impl Fn(T) -> TcResult<T>,
        subject_has_holes: impl Fn(T) -> bool,
    ) -> TcResult<T> {
        let mut subject = subject;
        for i in 0..MAX_INFER_ITERATIONS {
            match infer_subject(subject) {
                Ok(new_subject) => {
                    subject = new_subject;

                    // If we still have holes, then we need to infer again
                    if subject_has_holes(subject) {
                        continue;
                    }

                    // No holes, so we're done
                    break;
                }
                Err(TcError::Blocked) if i < MAX_INFER_ITERATIONS - 1 => {
                    // We're blocked on a hole, so try infer again as long as
                    // we haven't reached the maximum number of iterations
                    continue;
                }
                Err(err) => {
                    return Err(err);
                }
            }
        }
        Ok(subject)
    }
}

impl<'tc> AstPass for InferencePass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        // Infer the expression
        let (term, ty) = self.infer_loop(
            (self.ast_info().terms().get_data_by_node(node.id()).unwrap(), self.new_ty_hole()),
            |(term_id, ty_id)| self.inference_ops().infer_term(term_id, ty_id),
            |(term_id, ty_id)| {
                self.substitution_ops().atom_has_holes(term_id)
                    || self.substitution_ops().atom_has_holes(ty_id)
            },
        )?;

        // @@Temp:
        let evaluated = self.normalisation_ops().normalise(term.into())?;
        let evaluated_ty = self.normalisation_ops().normalise(ty.into())?;
        stream_less_writeln!("{}: {}", self.env().with(evaluated), self.env().with(evaluated_ty));

        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        // Infer the whole module
        let mod_def_id = self.infer_loop(
            self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap(),
            |mod_def_id| self.inference_ops().infer_mod_def(mod_def_id).map(|()| mod_def_id),
            |mod_def_id| self.substitution_ops().mod_def_has_holes(mod_def_id),
        )?;

        // @@Temp:
        stream_less_writeln!("{}", self.env().with(mod_def_id));

        Ok(())
    }
}
