//! Path-resolution for expressions.
//!
//! This uses the [super::paths] module to convert AST expression nodes that
//! correspond to paths into terms. It does not handle general expressions,
//! which is handled later.

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_types::new::{
    data::DataTy,
    environment::env::AccessToEnv,
    terms::{Term, TermId},
    tys::Ty,
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

    /// Make a term from the given [`ast::Expr`] and assign it to the node in
    /// the AST info store.
    ///
    /// This only handles expressions which are paths, and otherwise creates a
    /// hole to be resolved later.
    pub fn make_term_from_ast_expr(&self, node: AstNodeRef<ast::Expr>) -> TcResult<TermId> {
        let term_id = match self.expr_as_ast_path(node)? {
            Some(path) => match self.resolve_ast_path(&path)? {
                ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                        // Data type
                        self.new_term(Term::Ty(self.new_ty(Ty::Data(DataTy {
                            data_def: data_def_id,
                            args: data_def_args,
                        }))))
                    }
                    NonTerminalResolvedPathComponent::Mod(_, _) => {
                        // Modules are not allowed in value positions
                        return Err(TcError::CannotUseModuleInValuePosition {
                            location: self.node_location(node),
                        });
                    }
                },
                ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                    TerminalResolvedPathComponent::FnDef(fn_def_id) => {
                        // Reference to a function definition
                        self.new_term(Term::FnRef(fn_def_id))
                    }
                    TerminalResolvedPathComponent::CtorPat(_) => {
                        panic_on_span!(
                            self.node_location(node),
                            self.source_map(),
                            "found CtorPat in value ast path"
                        )
                    }
                    TerminalResolvedPathComponent::CtorTerm(ctor_term) => {
                        // Constructor
                        self.new_term(Term::Ctor(ctor_term))
                    }
                    TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                        // Function call
                        self.new_term(Term::FnCall(fn_call_term))
                    }
                    TerminalResolvedPathComponent::BoundVar(bound_var) => {
                        // Bound variable
                        self.new_term(Term::Var(bound_var))
                    }
                },
            },
            None => {
                // Not a path, we will resolve it later
                self.new_term_hole()
            }
        };

        self.ast_info().terms().insert(node.id(), term_id);
        Ok(term_id)
    }
}
