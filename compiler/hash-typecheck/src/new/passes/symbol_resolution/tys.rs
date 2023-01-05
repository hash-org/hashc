//! Path-resolution for types.
//!
//! This uses the [super::paths] module to convert AST type nodes that
//! correspond to paths into TC-types. It does not handle all types; non-path
//! types are handled later.

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_types::new::{
    data::DataTy,
    environment::env::AccessToEnv,
    terms::Term,
    tys::{Ty, TyId},
};

use super::{
    paths::{
        AstArgGroup, AstPath, AstPathComponent, NonTerminalResolvedPathComponent,
        ResolvedAstPathComponent, TerminalResolvedPathComponent,
    },
    SymbolResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::common::CommonOps,
    passes::ast_pass::AstPass,
};

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

    /// Make a type from the given [`ast::Ty`] and assign it to the node in
    /// the AST info store.
    ///
    /// This only handles types which are paths, and otherwise creates a
    /// hole to be resolved later.
    pub fn make_ty_from_ast_ty(&self, node: AstNodeRef<ast::Ty>) -> TcResult<TyId> {
        let ty_id = match self.ty_as_ast_path(node)? {
            Some(path) => match self.resolve_ast_path(&path)? {
                ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                        // Data type
                        self.new_ty(Ty::Data(DataTy { data_def: data_def_id, args: data_def_args }))
                    }
                    NonTerminalResolvedPathComponent::Mod(_, _) => {
                        // Modules are not allowed in type positions
                        return Err(TcError::CannotUseModuleInTypePosition {
                            location: self.node_location(node),
                        });
                    }
                },
                ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                    TerminalResolvedPathComponent::FnDef(_) => {
                        // Functions are not allowed in type positions
                        return Err(TcError::CannotUseFunctionInTypePosition {
                            location: self.node_location(node),
                        });
                    }
                    TerminalResolvedPathComponent::CtorPat(_) => {
                        panic_on_span!(
                            self.node_location(node),
                            self.source_map(),
                            "found CtorPat in type ast path"
                        )
                    }
                    TerminalResolvedPathComponent::CtorTerm(_) => {
                        // Constructors are not allowed in type positions
                        return Err(TcError::CannotUseConstructorInTypePosition {
                            location: self.node_location(node),
                        });
                    }
                    TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                        // Function call
                        self.new_ty(Ty::Eval(self.new_term(Term::FnCall(fn_call_term))))
                    }
                    TerminalResolvedPathComponent::Var(bound_var) => {
                        // Bound variable
                        self.new_ty(Ty::Var(bound_var.name))
                    }
                },
            },
            None => {
                // Not a path, we will resolve it later
                self.new_ty_hole()
            }
        };

        self.ast_info().tys().insert(node.id(), ty_id);
        Ok(ty_id)
    }
}
