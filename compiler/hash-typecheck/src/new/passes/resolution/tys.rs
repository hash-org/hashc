//! Resolution for types.
//!
//! This uses the [super::paths] module to convert AST type nodes that
//! correspond to paths into TC-types. It does not handle all types; non-path
//! types are handled later.

use std::iter::once;

use hash_ast::ast::{self, AstNodeRef, AstNodes};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::IDENTS, location::Span};
use hash_types::{
    new::{
        args::{ArgData, ArgsId},
        data::DataTy,
        environment::env::AccessToEnv,
        fns::FnCallTerm,
        params::{ParamData, ParamIndex, ParamsId},
        refs::{RefKind, RefTy},
        terms::Term,
        tuples::TupleTy,
        tys::{Ty, TyId},
    },
    ty_as_variant,
};
use hash_utils::store::CloneStore;
use itertools::Itertools;

use super::{
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    ResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
    passes::ast_utils::AstUtils,
};

impl<'tc> ResolutionPass<'tc> {
    /// Make TC arguments from the given set of AST type arguments.
    pub(super) fn make_args_from_ast_ty_args(
        &self,
        args: &ast::AstNodes<ast::TyArg>,
    ) -> TcResult<ArgsId> {
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
                    value: self.new_term(Term::Ty(self.make_ty_from_ast_ty(arg.ty.ast_ref())?)),
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(self.param_ops().create_args(args.into_iter()))
    }

    /// Make TC parameters from the given [`ast::TyArg`] list.
    fn make_params_from_ast_ty_args(&self, ty_args: &AstNodes<ast::TyArg>) -> TcResult<ParamsId> {
        let params = ty_args
            .ast_ref_iter()
            .filter_map(|ty_arg| {
                self.try_or_add_error(self.make_ty_from_ast_ty(ty_arg.ty.ast_ref())).map(|ty| {
                    ParamData {
                        name: self.new_symbol_from_ast_name(&ty_arg.name),
                        ty,
                        default_value: None,
                    }
                })
            })
            .collect_vec();

        if params.len() != ty_args.len() {
            Err(TcError::Signal)
        } else {
            Ok(self.param_ops().create_params(params.into_iter()))
        }
    }

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

    /// Make a type from the given [`ResolvedAstPathComponent`].
    fn make_ty_from_resolved_ast_path(
        &self,
        path: &ResolvedAstPathComponent,
        original_node_span: Span,
    ) -> TcResult<TyId> {
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                    // Data type
                    Ok(self
                        .new_ty(Ty::Data(DataTy { data_def: *data_def_id, args: *data_def_args })))
                }
                NonTerminalResolvedPathComponent::Mod(_, _) => {
                    // Modules are not allowed in type positions
                    Err(TcError::CannotUseModuleInTypePosition {
                        location: self.source_location(original_node_span),
                    })
                }
            },
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::FnDef(_) => {
                    // Functions are not allowed in type positions
                    Err(TcError::CannotUseFunctionInTypePosition {
                        location: self.source_location(original_node_span),
                    })
                }
                TerminalResolvedPathComponent::CtorPat(_) => {
                    panic_on_span!(
                        self.source_location(original_node_span),
                        self.source_map(),
                        "found CtorPat in type ast path"
                    )
                }
                TerminalResolvedPathComponent::CtorTerm(_) => {
                    // Constructors are not allowed in type positions
                    Err(TcError::CannotUseConstructorInTypePosition {
                        location: self.source_location(original_node_span),
                    })
                }
                TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                    // Function call
                    Ok(self.new_ty(Ty::Eval(self.new_term(Term::FnCall(*fn_call_term)))))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    // Bound variable
                    Ok(self.new_ty(Ty::Var(bound_var.name)))
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
    ) -> TcResult<Option<AstPath<'a>>> {
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
    fn make_ty_from_ast_access_ty(&self, node: AstNodeRef<ast::AccessTy>) -> TcResult<TyId> {
        let path = self.access_ty_as_ast_path(node)?;
        let resolved_path = self.resolve_ast_path(&path)?;
        self.make_ty_from_resolved_ast_path(&resolved_path, node.span())
    }

    /// Make a type from the given [`ast::NamedTy`].
    fn make_ty_from_ast_named_ty(&self, node: AstNodeRef<ast::NamedTy>) -> TcResult<TyId> {
        if node.name.is(IDENTS.Type) {
            Ok(self.new_small_universe_ty())
        } else {
            let path = self.named_ty_as_ast_path(node)?;
            let resolved_path = self.resolve_ast_path(&path)?;
            self.make_ty_from_resolved_ast_path(&resolved_path, node.span())
        }
    }

    /// Make a type from the given [`ast::TyFnCall`].
    fn make_ty_from_ast_ty_fn_call(&self, node: AstNodeRef<ast::TyFnCall>) -> TcResult<TyId> {
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
                        Ok(self.new_ty(Ty::Eval(self.new_term(Term::FnCall(FnCallTerm {
                            subject,
                            args,
                            implicit: true,
                        })))))
                    }
                    _ => Err(TcError::Signal),
                }
            }
        }
    }

    /// Make a type from the given [`ast::TupleTy`].
    fn make_ty_from_ast_tuple_ty(&self, node: AstNodeRef<ast::TupleTy>) -> TcResult<TyId> {
        // @@Todo: traverse parameters of tuple types in discovery
        let data = self.make_params_from_ast_ty_args(&node.entries)?;
        Ok(self.new_ty(Ty::Tuple(TupleTy { data })))
    }

    /// Make a type from the given [`ast::ListTy`].
    fn make_ty_from_ast_list_ty(&self, node: AstNodeRef<ast::ListTy>) -> TcResult<TyId> {
        let inner_ty = self.make_ty_from_ast_ty(node.inner.ast_ref())?;
        let list_def = self.primitives().list();
        Ok(self.new_ty(Ty::Data(DataTy {
            data_def: list_def,
            args: self.param_ops().create_positional_args_for_data_def(
                list_def,
                once(once(self.new_term(Term::Ty(inner_ty)))),
            ),
        })))
    }

    /// Make a type from the given [`ast::RefTy`].
    fn make_ty_from_ref_ty(&self, node: AstNodeRef<ast::RefTy>) -> TcResult<TyId> {
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
    pub(super) fn make_ty_from_ast_ty_fn_ty(&self, node: AstNodeRef<ast::TyFn>) -> TcResult<TyId> {
        // First, make the params
        let params = self.try_or_add_error(self.resolve_params_from_ast_params(&node.params, true));
        self.scoping().enter_ty_fn_ty(node, |ty_fn_id| {
            self.stores().ty().modify(ty_fn_id, |ty| {
                let ty_fn = ty_as_variant!(self, value ty, Fn);
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
                    (Some(_params), Some(_return_ty)) => Ok(ty_fn_id),
                    _ => Err(TcError::Signal),
                }
            })
        })
    }

    /// Make a type from the given [`ast::FnTy`].
    pub(super) fn make_ty_from_ast_fn_ty(&self, node: AstNodeRef<ast::FnTy>) -> TcResult<TyId> {
        // First, make the params
        let params = self.try_or_add_error(self.make_params_from_ast_ty_args(&node.params));
        self.scoping().enter_fn_ty(node, |fn_ty_id| {
            self.stores().ty().modify(fn_ty_id, |ty| {
                let fn_ty = ty_as_variant!(self, value ty, Fn);
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
                    (Some(_params), Some(_return_ty)) => Ok(fn_ty_id),
                    _ => Err(TcError::Signal),
                }
            })
        })
    }

    /// Make a type from the given [`ast::Ty`] and assign it to the node in
    /// the AST info store.
    ///
    /// This only handles types which are paths, and otherwise creates a
    /// hole to be resolved later.
    pub(super) fn make_ty_from_ast_ty(&self, node: AstNodeRef<ast::Ty>) -> TcResult<TyId> {
        let ty_id = match node.body {
            ast::Ty::Access(access_ty) => {
                self.make_ty_from_ast_access_ty(node.with_body(access_ty))?
            }
            ast::Ty::Named(named_ty) => self.make_ty_from_ast_named_ty(node.with_body(named_ty))?,
            ast::Ty::TyFnCall(ty_fn_call) => {
                self.make_ty_from_ast_ty_fn_call(node.with_body(ty_fn_call))?
            }
            ast::Ty::Tuple(tuple_ty) => self.make_ty_from_ast_tuple_ty(node.with_body(tuple_ty))?,
            ast::Ty::List(list_ty) => self.make_ty_from_ast_list_ty(node.with_body(list_ty))?,
            ast::Ty::Ref(ref_ty) => self.make_ty_from_ref_ty(node.with_body(ref_ty))?,
            ast::Ty::Fn(fn_ty) => self.make_ty_from_ast_fn_ty(node.with_body(fn_ty))?,
            ast::Ty::TyFn(ty_fn_ty) => self.make_ty_from_ast_ty_fn_ty(node.with_body(ty_fn_ty))?,
            ast::Ty::Union(_) | ast::Ty::Merge(_) => {
                // @@Todo: actually catch this at discovery, these are currently not supported.
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found merge type after discovery"
                )
            }
            ast::Ty::Set(_) | ast::Ty::Map(_) => {
                // @@Todo
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Sets and maps not implemented yet"
                )
            }
        };

        self.ast_info().tys().insert(node.id(), ty_id);
        Ok(ty_id)
    }
}
