use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_types::new::{environment::env::AccessToEnv, terms::TermId};

use super::{
    ast_paths::{AstArgGroup, AstPath, AstPathComponent},
    SymbolResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    ops::ast::AstOps,
};

/// This block converts AST nodes of different kinds into [`AstPath`]s, in order
/// to later resolve them into terms.
impl<'tc> SymbolResolutionPass<'tc> {
    /// Use the given [`ast::VariableExpr`] as a path.
    fn variable_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::VariableExpr>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.body.name.ident,
            name_span: node.span(),
            args: vec![],
            node_id: node.id(),
        }])
    }

    /// Use the given [`ast::AccessExpr`] as a path, if applicable.
    ///
    /// Otherwise, this might be a struct/tuple property access, which is not a
    /// path, and this will return `None`.
    pub fn access_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessExpr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match node.kind {
            ast::AccessKind::Namespace => match node.property.body() {
                ast::PropertyKind::NamedField(name) => {
                    let mut root =
                        self.expr_as_ast_path(node.body.subject.ast_ref())?.ok_or_else(|| {
                            TcError::InvalidNamespaceSubject { location: self.node_location(node) }
                        })?;
                    root.push(AstPathComponent {
                        name: *name,
                        name_span: node.property.span(),
                        args: vec![],
                        node_id: node.id(),
                    });
                    Ok(Some(root))
                }
                ast::PropertyKind::NumericField(_) => {
                    // Should have been caught at semantics
                    panic_on_span!(
                        self.node_location(node),
                        self.source_map(),
                        "Namespace followed by numeric field found"
                    )
                }
            },
            ast::AccessKind::Property => Ok(None),
        }
    }

    /// Use the given [`ast::ConstructorCallExpr`] as a path.
    fn constructor_call_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::ConstructorCallExpr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match self.expr_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut path) => match path.last_mut() {
                Some(component) => {
                    component.args.push(AstArgGroup::ExplicitArgs(&node.body.args));
                    Ok(Some(path))
                }
                None => panic!("Expected at least one path component"),
            },
            None => Ok(None),
        }
    }

    /// Use the given [`ast::Expr`] as a path, if possible.
    ///
    /// Returns `None` if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    pub fn expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Expr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Expr::Variable(variable_expr) => {
                let variable_ref = node.with_body(variable_expr);
                Ok(Some(self.variable_expr_as_ast_path(variable_ref)?))
            }
            ast::Expr::ConstructorCall(ctor_expr) => {
                let ctor_ref = node.with_body(ctor_expr);
                self.constructor_call_as_ast_path(ctor_ref)
            }
            ast::Expr::Access(access_expr) => {
                let access_ref = node.with_body(access_expr);
                self.access_expr_as_ast_path(access_ref)
            }
            ast::Expr::Ty(expr_ty) => {
                let expr_ty_ref = node.with_body(expr_ty.ty.body());
                self.ty_as_ast_path(expr_ty_ref)
            }
            _ => Ok(None),
        }
    }

    pub fn make_term_from_ast_expr(&self, _node: AstNodeRef<'_, ast::Expr>) -> TcResult<TermId> {
        // // For each node, try to resolve it as an ast path. If it is an ast path,
        // // it is added to the node.
        // match self.expr_as_ast_path(node) {
        //     Ok(Some(path)) => {
        //         // Resolve the path, which which adds it to the node.
        //         match self.resolve_ast_path(&path, node) {
        //             Ok(_) => {}
        //             Err(err) => {
        //                 self.diagnostics().add_error(err);
        //             }
        //         }
        //     }
        //     Ok(None) => {}
        //     Err(err) => {
        //         self.diagnostics().add_error(err);
        //     }
        // };
        todo!()
    }
}
