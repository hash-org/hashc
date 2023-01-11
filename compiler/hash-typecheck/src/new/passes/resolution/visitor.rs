//! AST visitor for the resolution pass.

use hash_ast::{
    ast::{self},
    ast_visitor_default_impl,
};

use super::ResolutionPass;
use crate::new::diagnostics::error::TcError;

impl ast::AstVisitor for ResolutionPass<'_> {
    type Error = TcError;
    ast_visitor_default_impl!(hiding: Module,);

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        self.resolve_ast_module_inner_terms(node)
    }
}
