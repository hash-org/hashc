/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
///
/// Any scoping errors are reported here.
use hash_ast::{ast, ast_visitor_default_impl, visitor::AstVisitor};

use super::ast_pass::AstPass;
use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcError, environment::tc_env::TcEnv},
};

pub struct SymbolResolutionPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(SymbolResolutionPass<'tc>);

impl<'tc> AstPass for SymbolResolutionPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_module(node)
    }
}

impl<'tc> SymbolResolutionPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env }
    }
}

impl ast::AstVisitor for SymbolResolutionPass<'_> {
    type Error = TcError;
    ast_visitor_default_impl!(hiding: Module,);

    type ModuleRet = ();
    fn visit_module(
        &self,
        _node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        Ok(())
    }
}
