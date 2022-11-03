use hash_ast::{ast, ast_visitor_default_impl};

pub struct SymbolResolvingPass {}
impl ast::AstVisitor for SymbolResolvingPass {
    type Error = ();
    ast_visitor_default_impl!(hiding: []);
}
