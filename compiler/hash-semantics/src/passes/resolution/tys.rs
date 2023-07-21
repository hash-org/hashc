//! Resolution for types.
//!
//! This uses the [super::paths] module to convert AST type nodes that
//! correspond to paths into TC-types. It does not handle all types; non-path
//! types are handled later.

use std::iter::once;

use hash_ast::ast::{self, AstNodeRef};
use hash_intrinsics::primitives::AccessToPrimitives;
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::IDENTS, location::SourceLocation};
use hash_tir::{
    args::{ArgData, ArgsId},
    data::DataTy,
    environment::env::AccessToEnv,
    fns::FnCallTerm,
    params::ParamIndex,
    refs::{RefKind, RefTy},
    terms::Term,
    tys::{Ty, TyId, TypeOfTerm},
    utils::{common::CommonUtils, AccessToUtils},
};

use super::{
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    ResolutionPass,
};
use crate::{
    diagnostics::error::{SemanticError, SemanticResult},
    ops::common::CommonOps,
};

impl<'tc> ResolutionPass<'tc> {
    /// Make TC arguments from the given set of AST type arguments.
    pub(super) fn make_args_from_ast_ty_args(
        &self,
        args: &ast::AstNodes<ast::TyArg>,
    ) -> SemanticResult<ArgsId> {
        // @@Todo: error recovery
        let args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(ArgData {
                    target: arg
                        .name
                        .as_ref()
                        .map(|name| ParamIndex::Name(name.ident))
                        .unwrap_or_else(|| ParamIndex::Position(i)),
                    value: self.use_ty_as_term(self.make_ty_from_ast_ty(arg.ty.ast_ref())?),
                })
            })
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(self.param_utils().create_args(args.into_iter()))
    }

    /// Use the given [`ast::NamedTy`] as a path.
    fn named_ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::NamedTy>,
    ) -> SemanticResult<AstPath<'a>> {
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
    ) -> SemanticResult<AstPath<'a>> {
        let mut root = self
            .ty_as_ast_path(node.body.subject.ast_ref())?
            .ok_or_else(|| SemanticError::InvalidNamespaceSubject { location: node.span() })?;

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
    ) -> SemanticResult<Option<AstPath<'a>>> {
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

    /// Make a type from the given [`ResolvedAstPathComponent`].
    fn make_ty_from_resolved_ast_path(
        &self,
        path: &ResolvedAstPathComponent,
        original_node_span: SourceLocation,
    ) -> SemanticResult<TyId> {
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                    // Data type
                    Ok(self
                        .new_ty(Ty::Data(DataTy { data_def: *data_def_id, args: *data_def_args })))
                }
                NonTerminalResolvedPathComponent::Mod(_) => {
                    // Modules are not allowed in type positions
                    Err(SemanticError::CannotUseModuleInTypePosition {
                        location: original_node_span,
                    })
                }
            },
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::FnDef(fn_def_id) => {
                    Ok(self.use_term_as_ty(self.new_term(Term::FnRef(*fn_def_id))))
                }
                TerminalResolvedPathComponent::CtorPat(_) => {
                    panic_on_span!(
                        original_node_span,
                        self.source_map(),
                        "found CtorPat in type ast path"
                    )
                }
                TerminalResolvedPathComponent::CtorTerm(ctor_term) => {
                    Ok(self.use_term_as_ty(self.new_term(Term::Ctor(*ctor_term))))
                }
                TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                    Ok(self.use_term_as_ty(self.new_term(Term::FnCall(*fn_call_term))))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    Ok(self.new_ty(Ty::Var(*bound_var)))
                }
            },
        }
    }

    /// Use the given [`ast::Ty`] as a path, if possible.
    ///
    /// Returns `None` if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    pub(super) fn ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Ty>,
    ) -> SemanticResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Ty::Access(access_ty) => {
                let access_ty_ref = node.with_body(access_ty);
                Ok(Some(self.access_ty_as_ast_path(access_ty_ref)?))
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

    /// Make a type from the given [`ast::AccessTy`].
    fn make_ty_from_ast_access_ty(&self, node: AstNodeRef<ast::AccessTy>) -> SemanticResult<TyId> {
        let path = self.access_ty_as_ast_path(node)?;
        let resolved_path = self.resolve_ast_path(&path)?;
        self.make_ty_from_resolved_ast_path(&resolved_path, node.span())
    }

    /// Make a type from the given [`ast::NamedTy`].
    fn make_ty_from_ast_named_ty(&self, node: AstNodeRef<ast::NamedTy>) -> SemanticResult<TyId> {
        if node.name.is(IDENTS.Type) {
            Ok(Ty::flexible_universe())
        } else if node.name.is(IDENTS.underscore) {
            Ok(Ty::hole())
        } else {
            let path = self.named_ty_as_ast_path(node)?;
            let resolved_path = self.resolve_ast_path(&path)?;
            self.make_ty_from_resolved_ast_path(&resolved_path, node.span())
        }
    }

    /// Make a type from the given [`ast::TyFnCall`].
    fn make_ty_from_ast_ty_fn_call(&self, node: AstNodeRef<ast::TyFnCall>) -> SemanticResult<TyId> {
        // This is either a path or a computed function call
        match self.ty_fn_call_as_ast_path(node)? {
            Some(path) => {
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_ty_from_resolved_ast_path(&resolved_path, node.span())
            }
            None => {
                let subject =
                    self.try_or_add_error(self.make_term_from_ast_expr(node.subject.ast_ref()));
                let args = self.try_or_add_error(self.make_args_from_ast_ty_args(&node.args));

                match (subject, args) {
                    (Some(subject), Some(args)) => {
                        Ok(self.use_term_as_ty(self.new_term(Term::FnCall(FnCallTerm {
                            subject,
                            args,
                            implicit: true,
                        }))))
                    }
                    _ => Err(SemanticError::Signal),
                }
            }
        }
    }

    /// Make a type from the given [`ast::TupleTy`].
    fn make_ty_from_ast_tuple_ty(&self, node: AstNodeRef<ast::TupleTy>) -> SemanticResult<TyId> {
        if node.entries.len() == 1 && node.entries[0].name.is_none() {
            // We treat this as a single type
            self.make_ty_from_ast_ty(node.entries[0].ty.ast_ref())
        } else {
            self.scoping().enter_tuple_ty(node, |mut tuple_ty| {
                tuple_ty.data = self.resolve_params_from_ast_ty_args(&node.entries)?;
                Ok(self.new_ty(tuple_ty))
            })
        }
    }

    /// Make a type from the given [`ast::ArrayTy`].
    fn make_ty_from_ast_array_ty(&self, node: AstNodeRef<ast::ArrayTy>) -> SemanticResult<TyId> {
        let inner_ty = self.make_ty_from_ast_ty(node.inner.ast_ref())?;
        match node.len.as_ref() {
            Some(len) => {
                let length_term = self.make_term_from_ast_expr(len.ast_ref())?;
                Ok(self.new_ty(Ty::Data(DataTy {
                    data_def: self.primitives().array(),
                    args: self
                        .param_utils()
                        .create_positional_args([self.use_ty_as_term(inner_ty), length_term]),
                })))
            }
            None => Ok(self.new_ty(Ty::Data(DataTy {
                data_def: self.primitives().list(),
                args: self
                    .param_utils()
                    .create_positional_args(once(self.use_ty_as_term(inner_ty))),
            }))),
        }
    }

    /// Make a type from the given [`ast::RefTy`].
    fn make_ty_from_ref_ty(&self, node: AstNodeRef<ast::RefTy>) -> SemanticResult<TyId> {
        let inner_ty = self.make_ty_from_ast_ty(node.inner.ast_ref())?;
        Ok(self.new_ty(Ty::Ref(RefTy {
            ty: inner_ty,
            kind: match node.kind.as_ref() {
                Some(kind) => match kind.body() {
                    ast::RefKind::Raw => RefKind::Raw,
                    ast::RefKind::Normal => RefKind::Local,
                },
                None => RefKind::Local,
            },
            mutable: match node.mutability.as_ref() {
                Some(mutability) => match mutability.body() {
                    ast::Mutability::Mutable => true,
                    ast::Mutability::Immutable => false,
                },
                None => false,
            },
        })))
    }

    /// Make a type from the given [`ast::Ty`].
    pub(super) fn make_ty_from_ast_ty_fn_ty(
        &self,
        node: AstNodeRef<ast::TyFn>,
    ) -> SemanticResult<TyId> {
        self.scoping().enter_ty_fn_ty(node, |mut ty_fn| {
            // First, make the params
            let params = self.try_or_add_error(self.resolve_params_from_ast_params(
                &node.params,
                true,
                ty_fn.into(),
            ));

            // Add the params if they exist
            if let Some(params) = params {
                ty_fn.params = params;
            }

            // Make the return type if it exists
            let return_ty =
                self.try_or_add_error(self.make_ty_from_ast_ty(node.return_ty.ast_ref()));
            if let Some(return_ty) = return_ty {
                ty_fn.return_ty = return_ty;
            }

            match (params, return_ty) {
                (Some(_params), Some(_return_ty)) => Ok(self.new_ty(ty_fn)),
                _ => Err(SemanticError::Signal),
            }
        })
    }

    /// Make a type from the given [`ast::FnTy`].
    pub(super) fn make_ty_from_ast_fn_ty(
        &self,
        node: AstNodeRef<ast::FnTy>,
    ) -> SemanticResult<TyId> {
        self.scoping().enter_fn_ty(node, |mut fn_ty| {
            // First, make the params
            let params = self.try_or_add_error(self.resolve_params_from_ast_ty_args(&node.params));

            // Add the params if they exist
            if let Some(params) = params {
                fn_ty.params = params;
            }

            // Make the return type if it exists
            let return_ty =
                self.try_or_add_error(self.make_ty_from_ast_ty(node.return_ty.ast_ref()));
            if let Some(return_ty) = return_ty {
                fn_ty.return_ty = return_ty;
            }

            match (params, return_ty) {
                (Some(_params), Some(_return_ty)) => Ok(self.new_ty(fn_ty)),
                _ => Err(SemanticError::Signal),
            }
        })
    }

    /// Make a type from the given [`ast::MergeTy`] and assign it to the node in
    /// the AST info store.
    ///
    /// We use merge types to represent propositional equality.
    pub(super) fn make_ty_from_merge_ty(
        &self,
        node: AstNodeRef<ast::MergeTy>,
    ) -> SemanticResult<TyId> {
        let lhs = self.make_ty_from_ast_ty(node.lhs.ast_ref())?;
        let rhs = self.make_ty_from_ast_ty(node.rhs.ast_ref())?;
        let typeof_lhs = self.new_term(TypeOfTerm { term: self.use_ty_as_term(lhs) });
        let args = self.param_utils().create_positional_args(vec![
            typeof_lhs,
            self.use_ty_as_term(lhs),
            self.use_ty_as_term(rhs),
        ]);
        Ok(self.new_ty(DataTy { data_def: self.primitives().equal(), args }))
    }

    /// Make a type from the given [`ast::Ty`] and assign it to the node in
    /// the AST info store.
    ///
    /// This only handles types which are paths, and otherwise creates a
    /// hole to be resolved later.
    pub(super) fn make_ty_from_ast_ty(&self, node: AstNodeRef<ast::Ty>) -> SemanticResult<TyId> {
        let ty_id = match node.body {
            ast::Ty::Access(access_ty) => {
                self.make_ty_from_ast_access_ty(node.with_body(access_ty))?
            }
            ast::Ty::Named(named_ty) => self.make_ty_from_ast_named_ty(node.with_body(named_ty))?,
            ast::Ty::TyFnCall(ty_fn_call) => {
                self.make_ty_from_ast_ty_fn_call(node.with_body(ty_fn_call))?
            }
            ast::Ty::Tuple(tuple_ty) => self.make_ty_from_ast_tuple_ty(node.with_body(tuple_ty))?,
            ast::Ty::Array(list_ty) => self.make_ty_from_ast_array_ty(node.with_body(list_ty))?,
            ast::Ty::Ref(ref_ty) => self.make_ty_from_ref_ty(node.with_body(ref_ty))?,
            ast::Ty::Fn(fn_ty) => self.make_ty_from_ast_fn_ty(node.with_body(fn_ty))?,
            ast::Ty::TyFn(ty_fn_ty) => self.make_ty_from_ast_ty_fn_ty(node.with_body(ty_fn_ty))?,
            ast::Ty::Merge(merge_ty) => self.make_ty_from_merge_ty(node.with_body(merge_ty))?,
            ast::Ty::Expr(expr) => {
                let expr = self.make_term_from_ast_expr(expr.expr.ast_ref())?;
                self.new_ty(expr)
            }
            ast::Ty::Union(_) => {
                panic_on_span!(node.span(), self.source_map(), "Found union type after discovery")
            }
        };

        self.ast_info().tys().insert(node.id(), ty_id);
        self.stores().location().add_location_to_target(ty_id, node.span());
        Ok(ty_id)
    }
}
