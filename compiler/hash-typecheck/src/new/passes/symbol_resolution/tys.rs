use hash_ast::ast::{self, AstNodeRef};
use hash_types::new::tys::TyId;

use super::{
    ast_paths::{AstArgGroup, AstPath, AstPathComponent},
    SymbolResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    passes::ast_pass::AstPass,
};

/// This block converts AST nodes of different kinds into [`AstPath`]s, in order
/// to later resolve them into terms.
impl<'tc> SymbolResolutionPass<'tc> {
    /// Use the given [`ast::NamedTy`] as a path.
    fn named_ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::NamedTy>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.body.name.ident,
            name_span: node.span(),
            args: vec![],
            node_id: node.id(),
        }])
    }

    /// Use the given [`ast::AccessTy`] as a path.
    fn access_ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessTy>,
    ) -> TcResult<AstPath<'a>> {
        let mut root = self.ty_as_ast_path(node.body.subject.ast_ref())?.ok_or_else(|| {
            TcError::InvalidNamespaceSubject { location: self.node_location(node) }
        })?;

        root.push(AstPathComponent {
            name: node.body.property.ident,
            name_span: node.body.property.span(),
            args: vec![],
            node_id: node.id(),
        });
        Ok(root)
    }

    /// Use the given [`ast::TyFnCall`] as a path.
    fn ty_fn_call_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::TyFnCall>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match self.expr_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut path) => match path.last_mut() {
                Some(component) => {
                    component.args.push(AstArgGroup::ImplicitArgs(&node.body.args));
                    Ok(Some(path))
                }
                None => panic!("Expected at least one path component"),
            },
            None => Ok(None),
        }
    }

    /// Use the given [`ast::Ty`] as a path, if possible.
    ///
    /// Returns `None` if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    pub fn ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Ty>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Ty::Access(access_ty) => {
                let access_ref = node.with_body(access_ty);
                Ok(Some(self.access_ty_as_ast_path(access_ref)?))
            }
            ast::Ty::Named(named_ty) => {
                let named_ref = node.with_body(named_ty);
                Ok(Some(self.named_ty_as_ast_path(named_ref)?))
            }
            ast::Ty::TyFnCall(ty_fn_call) => {
                let ty_fn_call_ref = node.with_body(ty_fn_call);
                self.ty_fn_call_as_ast_path(ty_fn_call_ref)
            }
            _ => Ok(None),
        }
    }

    pub fn make_ty_from_ast_ty(&self, _node: AstNodeRef<'_, ast::Ty>) -> TcResult<TyId> {
        // // For each node, try to resolve it as an ast path. If it is an ast path,
        // // it is added to the node.
        // match self.ty_as_ast_path(node) {
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
        // Ok(())
        todo!()
    }
}
