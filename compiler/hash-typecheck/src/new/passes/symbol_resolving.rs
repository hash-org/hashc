use hash_ast::{ast, ast_visitor_default_impl};

use crate::{diagnostics::error::TcError, impl_access_to_tc_env, new::data::env::TcEnv};

pub struct SymbolResolvingPass<'env> {
    env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(SymbolResolvingPass<'env>);

impl<'env> SymbolResolvingPass<'env> {
    pub fn new(env: &'env TcEnv<'env>) -> Self {
        Self { env }
    }
}

impl<'env> ast::AstVisitor for SymbolResolvingPass<'env> {
    type Error = TcError;
    ast_visitor_default_impl!(hiding: Declaration, Module, ModBlock);

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        _node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        todo!()
    }

    type ModuleRet = ();
    fn visit_module(
        &self,
        _node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        todo!()
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &self,
        _node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        todo!()
    }
}
