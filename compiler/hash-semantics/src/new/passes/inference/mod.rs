//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use derive_more::Constructor;
use hash_ast::ast;
use hash_tir::{
    environment::env::AccessToEnv, locations::LocationTarget, utils::common::CommonUtils,
};
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

impl InferencePass<'_> {
    /// Infer the given subject by the provided closure, or error if it contains
    /// holes.
    fn infer_fully<T: Copy>(
        &self,
        subject: T,
        infer_subject: impl Fn(T) -> TcResult<T>,
        subject_has_holes: impl Fn(T) -> bool,
        location: impl Fn(T) -> LocationTarget,
    ) -> TcResult<T> {
        let subject = infer_subject(subject)?;

        // If we have holes, error
        if subject_has_holes(subject) {
            return Err(TcError::NeedMoreTypeAnnotationsToInfer { term: location(subject) });
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
        let (term, _) = self.infer_fully(
            (self.ast_info().terms().get_data_by_node(node.id()).unwrap(), self.new_ty_hole()),
            |(term_id, ty_id)| self.inference_ops().infer_term(term_id, ty_id),
            |(term_id, ty_id)| {
                self.substitution_ops().atom_has_holes(term_id)
                    || self.substitution_ops().atom_has_holes(ty_id)
            },
            |(term_id, _)| term_id.into(),
        )?;

        // @@Temp:
        let evaluated = self.normalisation_ops().normalise(term.into())?;
        stream_less_writeln!("{}", self.env().with(evaluated));

        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        // Infer the whole module
        let mod_def_id = self.infer_fully(
            self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap(),
            |mod_def_id| self.inference_ops().infer_mod_def(mod_def_id).map(|()| mod_def_id),
            |mod_def_id| self.substitution_ops().mod_def_has_holes(mod_def_id),
            |mod_def_id| mod_def_id.into(),
        )?;

        stream_less_writeln!("{}", self.env().with(mod_def_id));

        // @@Todo: #entry_point directive and main type checking
        //
        // if let Some(kind) =
        //     self.source_map().module_kind_by_id(self.current_source_info().source_id)
        // {
        //     match kind {
        //         ModuleKind::Normal => {}
        //         ModuleKind::Prelude => {}
        //         ModuleKind::EntryPoint => {
        //             // Check that the module has a `main` function
        //             if let Some(fn_def_id) =
        //                 self.mod_utils().get_mod_fn_member_by_ident(mod_def_id,
        // "main")             {
        //                 let _call_term = self.new_term(FnCallTerm {
        //                     subject: self.new_term(fn_def_id),
        //                     implicit: false,
        //                     args: self.new_empty_args(),
        //                 });

        //                 // let (inferred_call_term, _) =
        //                 //     self.inference_ops().infer_term(call_term,
        //                 // self.new_void_ty())?; let _ =
        //                 // self.normalisation_ops().
        //                 // normalise(inferred_call_term.into())?;
        //             }
        //         }
        //     }
        // }

        Ok(())
    }
}
