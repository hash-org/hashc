//! Resolution of AST parameters and arguments to terms.

use hash_ast::ast::{self, AstNodeId, AstNodeRef};
use hash_source::location::Span;
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey,
};
use hash_tir::nodes::{
    args::{ArgsId, PatArgsId},
    node::{Node, NodeOrigin},
    params::{Param, ParamId, ParamsId, SomeParamsOrArgsId},
    pats::Spread,
    terms::{fns::CallTerm, Term, TermId, Ty},
};

use super::ResolutionPass;
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

/// An argument group in the AST.
#[derive(Copy, Clone, Debug)]
pub enum AstArgGroup<'a> {
    /// A group of explicit `(a, b, c)` arguments.
    ExplicitArgs(&'a ast::AstNodes<ast::ExprArg>),
    /// A group of tuple `(a, b, c)` arguments
    TupleArgs(&'a ast::AstNodes<ast::TupleLitEntry>),
    /// A group of implicit `<a, b, c>` arguments.
    ImplicitArgs(&'a ast::AstNodes<ast::TyArg>),
    /// A group of explicit `(p, q, r)` pattern arguments
    ExplicitPatArgs(&'a ast::AstNodes<ast::PatArg>, &'a Option<ast::AstNode<ast::SpreadPat>>),
    // @@Todo: implicit pattern arguments when AST supports this
}

impl AstArgGroup<'_> {
    /// Get the span of this argument group.
    pub fn span(&self) -> Span {
        match self {
            AstArgGroup::ExplicitArgs(args) => args.span(),
            AstArgGroup::ImplicitArgs(args) => args.span(),
            AstArgGroup::ExplicitPatArgs(args, spread) => spread
                .as_ref()
                .map_or_else(|| args.span(), |spread| args.span().join(spread.span())),
            AstArgGroup::TupleArgs(args) => args.span(),
        }
    }

    /// Whether the group is implicit (angle brackets).
    pub fn is_implicit(&self) -> bool {
        matches!(self, AstArgGroup::ImplicitArgs(_))
    }
}

/// Resolved arguments.
///
/// These are either term arguments, or pattern arguments.
#[derive(Copy, Clone, Debug)]
pub enum ResolvedArgs {
    Term(ArgsId),
    Pat(PatArgsId, Option<Spread>),
}

impl ResolvedArgs {
    /// Get the number of arguments.
    pub fn len(&self) -> usize {
        match self {
            ResolvedArgs::Term(args) => args.len(),
            ResolvedArgs::Pat(args, _) => args.len(),
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl From<ResolvedArgs> for SomeParamsOrArgsId {
    fn from(value: ResolvedArgs) -> Self {
        match value {
            ResolvedArgs::Term(args) => SomeParamsOrArgsId::Args(args),
            ResolvedArgs::Pat(args, _) => SomeParamsOrArgsId::PatArgs(args),
        }
    }
}

impl<E: SemanticEnv> ResolutionPass<'_, E> {
    /// Resolve the given AST ty-arg parameter into [`ParamId`].
    /// Same assumptions as [`Self::resolve_param_from_ast_param`].
    fn resolve_param_from_ast_ty_param(
        &self,
        ast_param: AstNodeRef<ast::TyParam>,
    ) -> SemanticResult<ParamId> {
        // Resolve the default value and type annotation:
        let resolved_ty = self.try_or_add_error(
            ast_param.ty.as_ref().map(|ty| self.make_ty_from_ast_ty(ty.ast_ref())).unwrap_or_else(
                || {
                    // Default as "Type"
                    Ok(Ty::universe(NodeOrigin::InferredFrom(ast_param.id())))
                },
            ),
        );

        // Get the existing param id from the AST info store:
        let param_id = self.ast_info.params().get_data_by_node(ast_param.id()).unwrap();

        match resolved_ty {
            Some(resolved_ty) => {
                param_id.borrow_mut().ty = resolved_ty;
                Ok(param_id)
            }
            _ => Err(SemanticError::Signal),
        }
    }

    /// Resolve the given AST parameter into [`ParamId`].
    ///
    /// This assumes that this was initially traversed during
    /// discovery, and is set in the AST info store. It gets the existing
    /// parameter definition and enriches it with the resolved type and
    /// default value.
    fn resolve_param_from_ast_param(
        &self,
        ast_param: AstNodeRef<ast::Param>,
        implicit: bool,
    ) -> SemanticResult<ParamId> {
        // Resolve the default value and type annotation:
        let default_value = self.try_or_add_error(
            ast_param
                .default
                .as_ref()
                .map(|default_value| self.make_term_from_ast_expr(default_value.ast_ref()))
                .transpose(),
        );
        let resolved_ty = self.try_or_add_error(
            ast_param
                .ty
                .as_ref()
                .map(|ty| self.make_ty_from_ast_ty(ty.ast_ref()))
                .or_else(|| {
                    if implicit {
                        // Default as "Type"
                        Some(Ok(Ty::universe(NodeOrigin::InferredFrom(ast_param.id()))))
                    } else {
                        None
                    }
                })
                .transpose(),
        );

        // Get the existing param id from the AST info store:
        let param_id = self.ast_info.params().get_data_by_node(ast_param.id()).unwrap();
        match (resolved_ty, default_value) {
            (Some(resolved_ty), Some(resolved_default_value)) => {
                let mut param = param_id.borrow_mut();

                // If this is None, it wasn't given as an annotation, so we just leave it as
                // a hole
                if let Some(resolved_ty) = resolved_ty {
                    param.ty = resolved_ty;
                }
                param.default = resolved_default_value;

                Ok(param_id)
            }
            _ => Err(SemanticError::Signal),
        }
    }

    /// Resolve the given set of AST ty-arg parameters into [`ParamsId`].
    ///
    /// This assumes that the parameters were initially traversed during
    /// discovery, and are set in the AST info store.
    pub(super) fn resolve_params_from_ast_ty_params(
        &self,
        node: &ast::AstNode<ast::TyParams>,
    ) -> SemanticResult<ParamsId> {
        let mut found_error = false;
        let mut params_id: Option<ParamsId> = None;

        for ast_param in node.params.ast_ref_iter() {
            let param_id = self.try_or_add_error(self.resolve_param_from_ast_ty_param(ast_param));
            match param_id {
                Some(param_id) => {
                    // Remember the params ID to return at the end
                    self.scoping().add_param_binding(param_id);
                    params_id =
                        Some(Node::create_at(param_id.0, NodeOrigin::Given(ast_param.id())));
                }
                None => {
                    // Continue resolving the rest of the parameters and report the error at the
                    // end.
                    found_error = true;
                }
            }
        }

        if found_error {
            Err(SemanticError::Signal)
        } else {
            Ok(params_id.unwrap_or_else(|| {
                Node::create_at(Node::<Param>::empty_seq(), NodeOrigin::Given(node.id()))
            }))
        }
    }

    /// Resolve the given set of AST parameters into [`ParamsId`].
    ///
    /// This assumes that the parameters were initially traversed during
    /// discovery, and are set in the AST info store.
    pub(super) fn resolve_params_from_ast_params(
        &self,
        node: &ast::AstNode<ast::Params>,
        implicit: bool,
    ) -> SemanticResult<ParamsId> {
        let mut found_error = false;
        let mut params_id: Option<ParamsId> = None;

        for ast_param in node.params.ast_ref_iter() {
            let param_id =
                self.try_or_add_error(self.resolve_param_from_ast_param(ast_param, implicit));
            match param_id {
                Some(param_id) => {
                    // Remember the params ID to return at the end
                    self.scoping().add_param_binding(param_id);
                    params_id =
                        Some(Node::create_at(param_id.0, NodeOrigin::Given(ast_param.id())));
                }
                None => {
                    // Continue resolving the rest of the parameters and report the error at the
                    // end.
                    found_error = true;
                }
            }
        }

        if found_error {
            Err(SemanticError::Signal)
        } else {
            Ok(params_id.unwrap_or_else(|| {
                Node::create_at(Node::<Param>::empty_seq(), NodeOrigin::Given(node.id()))
            }))
        }
    }

    /// Make [`ResolvedArgs`] from an AST argument group.
    ///
    /// This will return either pattern arguments or term arguments, depending
    /// on the kind of the argument group.
    pub(super) fn make_args_from_ast_arg_group(
        &self,
        group: &AstArgGroup,
    ) -> SemanticResult<ResolvedArgs> {
        match group {
            AstArgGroup::ExplicitArgs(args) => {
                Ok(ResolvedArgs::Term(self.make_args_from_constructor_call_args(args)?))
            }
            AstArgGroup::ImplicitArgs(args) => {
                Ok(ResolvedArgs::Term(self.make_args_from_ast_ty_args(args)?))
            }
            AstArgGroup::TupleArgs(args) => {
                Ok(ResolvedArgs::Term(self.make_args_from_ast_tuple_lit_args(args)?))
            }
            AstArgGroup::ExplicitPatArgs(pat_args, spread) => {
                let pat_args =
                    self.try_or_add_error(self.make_pat_args_from_ast_pat_args(pat_args));
                let spread = self.try_or_add_error(self.make_spread_from_ast_spread(spread));
                match (pat_args, spread) {
                    (Some(pat_args), Some(spread)) => Ok(ResolvedArgs::Pat(pat_args, spread)),
                    _ => Err(SemanticError::Signal),
                }
            }
        }
    }

    /// Wrap a term in a function call, given a list of arguments as a list of
    /// [`AstArgGroup`].
    ///
    /// Creates a new [`TermId`], which is a term that represents the
    /// function call, and might be nested depending on `args`.
    ///
    /// It is not valid for `args` to be pattern arguments, and it will produce
    /// an error if it is.
    ///
    /// If `args` is empty, this will panic.
    pub(super) fn wrap_term_in_fn_call_from_ast_args(
        &self,
        subject: TermId,
        args: &[AstArgGroup],
        original_node_id: AstNodeId,
    ) -> SemanticResult<CallTerm> {
        debug_assert!(!args.is_empty());
        let mut current_subject = subject;
        for arg_group in args {
            let args = self.make_args_from_ast_arg_group(arg_group)?;

            match args {
                ResolvedArgs::Term(args) => {
                    // Here we are trying to call a function with term arguments.
                    // Apply the arguments to the current subject and continue.
                    current_subject = Term::from(
                        Term::Call(CallTerm {
                            subject: current_subject,
                            args,
                            implicit: matches!(arg_group, AstArgGroup::ImplicitArgs(_)),
                        }),
                        NodeOrigin::Given(original_node_id),
                    );
                }
                ResolvedArgs::Pat(_, _) => {
                    // Here we are trying to call a function with pattern arguments.
                    // This is not allowed.
                    return Err(SemanticError::CannotUseFunctionInPatternPosition {
                        location: original_node_id.span(),
                    });
                }
            }
        }
        match *current_subject.value() {
            Term::Call(call) => Ok(call),
            _ => unreachable!(),
        }
    }
}
