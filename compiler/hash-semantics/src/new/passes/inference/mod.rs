//! The third pass of the typechecker, which infers all remaining terms and
//! types in the program.
//!
//! Typing errors are reported during this pass.

use derive_more::Constructor;
use hash_ast::ast::{self};
use hash_tir::new::environment::env::AccessToEnv;
use hash_typecheck::AccessToTypechecking;

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

impl<'tc> AstPass for InferencePass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        // Just infer the term corresponding to the body block, and then print it
        // (@@Temp)
        let term = self.ast_info().terms().get_data_by_node(node.id()).unwrap();
        let ty = self.infer_ops().infer_term(term)?;
        let ty_str = match ty {
            Some(ty) => self.env().with(ty).to_string(),
            None => "<unknown>".to_string(),
        };
        println!("{}: {}", self.env().with(term), ty_str);
        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        // Infer the whole module, which includes each member, and then print it
        // (@@Temp)
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.infer_ops().infer_mod_def(mod_def_id)?;
        println!("{}", self.env().with(mod_def_id));
        Ok(())
    }
}
