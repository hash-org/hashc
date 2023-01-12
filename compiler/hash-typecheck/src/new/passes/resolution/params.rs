//! Resolution of AST parameters and arguments to terms.

use std::{iter::empty, ops::Range};

use hash_ast::ast::{self, AstNodeRef};
use hash_source::location::Span;
use hash_types::new::{
    args::{ArgsId, PatArgsId},
    defs::{DefArgGroupData, DefArgsId, DefParamsId, DefPatArgGroupData, DefPatArgsId},
    environment::env::AccessToEnv,
    fns::FnCallTerm,
    params::{ParamId, ParamsId},
    pats::Spread,
    terms::{Term, TermId},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey};

use super::ResolutionPass;
use crate::new::{
    diagnostics::{
        error::{TcError, TcResult},
        params::{SomeArgsId, SomeDefArgsId},
    },
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
    passes::ast_utils::AstUtils,
};

/// An argument group in the AST.
#[derive(Copy, Clone, Debug)]
pub enum AstArgGroup<'a> {
    /// A group of explicit `(a, b, c)` arguments.
    ExplicitArgs(&'a ast::AstNodes<ast::ConstructorCallArg>),
    /// A group of tuple `(a, b, c)` arguments
    TupleArgs(&'a ast::AstNodes<ast::TupleLitEntry>),
    /// A group of implicit `<a, b, c>` arguments.
    ImplicitArgs(&'a ast::AstNodes<ast::TyArg>),
    /// A group of explicit `(p, q, r)` pattern arguments
    ExplicitPatArgs(
        &'a ast::AstNodes<ast::TuplePatEntry>,
        &'a Option<ast::AstNode<ast::SpreadPat>>,
    ),
    // @@Todo: implicit pattern arguments when AST supports this
}

impl AstArgGroup<'_> {
    /// Get the span of this argument group.
    pub fn span(&self) -> Option<Span> {
        match self {
            AstArgGroup::ExplicitArgs(args) => args.span(),
            AstArgGroup::ImplicitArgs(args) => args.span(),
            AstArgGroup::ExplicitPatArgs(args, spread) => args
                .span()
                .and_then(|args_span| Some(args_span.join(spread.as_ref()?.span())))
                .or_else(|| Some(spread.as_ref()?.span())),
            AstArgGroup::TupleArgs(args) => args.span(),
        }
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
    fn len(&self) -> usize {
        match self {
            ResolvedArgs::Term(args) => args.len(),
            ResolvedArgs::Pat(args, _) => args.len(),
        }
    }
}

impl From<ResolvedArgs> for SomeArgsId {
    fn from(value: ResolvedArgs) -> Self {
        match value {
            ResolvedArgs::Term(args) => SomeArgsId::Args(args),
            ResolvedArgs::Pat(args, _) => SomeArgsId::PatArgs(args),
        }
    }
}

/// Resolved definition arguments.
///
/// These are either term arguments, or pattern arguments.
#[derive(Copy, Clone, Debug)]
pub enum ResolvedDefArgs {
    Term(DefArgsId),
    Pat(DefPatArgsId),
}

impl From<ResolvedDefArgs> for SomeDefArgsId {
    fn from(value: ResolvedDefArgs) -> Self {
        match value {
            ResolvedDefArgs::Term(args) => SomeDefArgsId::Args(args),
            ResolvedDefArgs::Pat(args) => SomeDefArgsId::PatArgs(args),
        }
    }
}

impl ResolvedDefArgs {
    /// Get the number of arguments.
    pub fn len(&self) -> usize {
        match self {
            ResolvedDefArgs::Term(args) => args.len(),
            ResolvedDefArgs::Pat(args) => args.len(),
        }
    }

    /// Check if there are no arguments.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the range of indices of the arguments.
    pub fn to_index_range(&self) -> Range<usize> {
        match self {
            ResolvedDefArgs::Term(args) => args.to_index_range(),
            ResolvedDefArgs::Pat(args) => args.to_index_range(),
        }
    }
}

impl<'tc> ResolutionPass<'tc> {
    /// Resolve the given set of AST definition parameters into [`DefParamsId`].
    ///
    /// This assumes that the parameters were initially traversed during
    /// discovery, and are set in the AST info store.
    ///
    /// Note that this does not return the [`DefParamsId`] as it is inaccessible
    /// just from the node itself. @@Improvement: store this in the AST info
    /// store which means that it should have its own Node ID.
    pub(super) fn _resolve_def_params_from_ast_param_groups<'a>(
        &self,
        ast_def_params: impl Iterator<Item = &'a ast::AstNodes<ast::Param>>,
        implicit: bool,
    ) -> TcResult<()> {
        let mut found_error = false;
        for ast_def_param_group in ast_def_params {
            if self
                .try_or_add_error(
                    self.resolve_params_from_ast_params(ast_def_param_group, implicit),
                )
                .is_none()
            {
                found_error = true;
            }
        }
        if found_error {
            Err(TcError::Signal)
        } else {
            Ok(())
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
    ) -> TcResult<ParamId> {
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
                        Some(Ok(self.new_small_universe_ty()))
                    } else {
                        None
                    }
                })
                .transpose(),
        );

        // Get the existing param id from the AST info store:
        let param_id = self.ast_info().params().get_data_by_node(ast_param.id()).unwrap();
        match (resolved_ty, default_value) {
            (Some(resolved_ty), Some(resolved_default_value)) => {
                self.stores().params().modify_fast(param_id.0, |params| {
                    // If this is None, it wasn't given as an annotation, so we just leave it as
                    // a hole
                    if let Some(resolved_ty) = resolved_ty {
                        params[param_id.1].ty = resolved_ty;
                    }
                    params[param_id.1].default_value = resolved_default_value;
                });

                Ok(param_id)
            }
            _ => Err(TcError::Signal),
        }
    }

    /// Resolve the given set of AST parameters into [`ParamsId`].
    ///
    /// This assumes that the parameters were initially traversed during
    /// discovery, and are set in the AST info store.
    pub(super) fn resolve_params_from_ast_params(
        &self,
        params: &ast::AstNodes<ast::Param>,
        implicit: bool,
    ) -> TcResult<ParamsId> {
        let mut found_error = false;
        let mut params_id: Option<ParamsId> = None;

        for ast_param in params.ast_ref_iter() {
            let param_id =
                self.try_or_add_error(self.resolve_param_from_ast_param(ast_param, implicit));
            match param_id {
                Some(param_id) => {
                    // Remember the params ID to return at the end
                    params_id = Some(param_id.0);
                }
                None => {
                    // Continue resolving the rest of the parameters and report the error at the
                    // end.
                    found_error = true;
                }
            }
        }

        if found_error {
            Err(TcError::Signal)
        } else {
            Ok(params_id.unwrap_or_else(|| self.new_empty_params()))
        }
    }

    /// Make [`ResolvedArgs`] from an AST argument group.
    ///
    /// This will return either pattern arguments or term arguments, depending
    /// on the kind of the argument group.
    pub(super) fn make_args_from_ast_arg_group(
        &self,
        group: &AstArgGroup,
    ) -> TcResult<ResolvedArgs> {
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
                    _ => Err(TcError::Signal),
                }
            }
        }
    }

    /// Make [`ResolvedDefArgs`] from a list of AST argument groups, using
    /// `make_args_from_ast_arg_group` to make each argument group.
    ///
    /// Panics if the argument group list is empty.
    ///
    /// This will either create term arguments or pattern arguments, depending
    /// on the argument groups given. If they mismatch in kinds, an error is
    /// returned.
    pub(super) fn make_def_args_from_ast_arg_groups(
        &self,
        groups: &[AstArgGroup],
        originating_params: DefParamsId,
    ) -> TcResult<ResolvedDefArgs> {
        let mut is_pat_args: Option<bool> = None;

        // Ensure that each argument group is of the same kind.
        for group in groups {
            match (group, is_pat_args) {
                (AstArgGroup::ExplicitArgs(_) | AstArgGroup::ImplicitArgs(_), None) => {
                    is_pat_args = Some(false);
                }
                (AstArgGroup::ExplicitPatArgs(_, _), None) => {
                    is_pat_args = Some(true);
                }
                // Correct cases:
                (AstArgGroup::ExplicitArgs(_) | AstArgGroup::ImplicitArgs(_), Some(false))
                | (AstArgGroup::ExplicitPatArgs(_, _), Some(true)) => {}
                // Error cases:
                (AstArgGroup::ExplicitArgs(_) | AstArgGroup::ImplicitArgs(_), Some(true))
                | (AstArgGroup::ExplicitPatArgs(_, _), Some(false)) => {
                    // @@Correctness: should we make this a user error or will it never happen?
                    panic!("Mixing pattern and non-pattern arguments is not allowed")
                }
                (AstArgGroup::TupleArgs(_), _) => {
                    panic!("Found tuple arguments in def args")
                }
            }
        }

        match is_pat_args {
            Some(is_pat_args) => {
                if is_pat_args {
                    // Pattern arguments
                    let arg_groups = groups
                        .iter()
                        .enumerate()
                        .map(|(index, group)| {
                            let (pat_args, spread) =
                                match self.make_args_from_ast_arg_group(group)? {
                                    ResolvedArgs::Term(_) => unreachable!(),
                                    ResolvedArgs::Pat(pat_args, spread) => (pat_args, spread),
                                };
                            Ok(DefPatArgGroupData {
                                pat_args,
                                spread,
                                param_group: (originating_params, index),
                            })
                        })
                        .collect::<TcResult<Vec<_>>>()?;
                    let def_pat_args = self.param_ops().create_def_pat_args(arg_groups.into_iter());
                    self.stores().location().add_locations_to_targets(def_pat_args, |i| {
                        Some(self.source_location(groups[i].span()?))
                    });
                    Ok(ResolvedDefArgs::Pat(def_pat_args))
                } else {
                    // Term arguments
                    let arg_groups = groups
                        .iter()
                        .enumerate()
                        .map(|(index, group)| {
                            let args = match self.make_args_from_ast_arg_group(group)? {
                                ResolvedArgs::Term(term_args) => term_args,
                                ResolvedArgs::Pat(_, _) => unreachable!(),
                            };
                            Ok(DefArgGroupData { args, param_group: (originating_params, index) })
                        })
                        .collect::<TcResult<Vec<_>>>()?;
                    let def_args = self.param_ops().create_def_args(arg_groups.into_iter());
                    self.stores().location().add_locations_to_targets(def_args, |i| {
                        Some(self.source_location(groups[i].span()?))
                    });
                    Ok(ResolvedDefArgs::Term(def_args))
                }
            }
            // @@Hack: here we assume the args are term args; if they are meant to be pattern args
            // it will be handled in [`super::pats`].
            None => Ok(ResolvedDefArgs::Term(self.param_ops().create_def_args(empty()))),
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
        original_span: Span,
    ) -> TcResult<FnCallTerm> {
        debug_assert!(!args.is_empty());
        let mut current_subject = subject;
        for arg_group in args {
            let args = self.make_args_from_ast_arg_group(arg_group)?;

            match args {
                ResolvedArgs::Term(args) => {
                    // Here we are trying to call a function with term arguments.
                    // Apply the arguments to the current subject and continue.
                    current_subject = self.new_term(Term::FnCall(FnCallTerm {
                        subject: current_subject,
                        args,
                        implicit: matches!(arg_group, AstArgGroup::ImplicitArgs(_)),
                    }));
                }
                ResolvedArgs::Pat(_, _) => {
                    // Here we are trying to call a function with pattern arguments.
                    // This is not allowed.
                    return Err(TcError::CannotUseFunctionInPatternPosition {
                        location: self.source_location(original_span),
                    });
                }
            }
        }
        match self.get_term(current_subject) {
            Term::FnCall(call) => Ok(call),
            _ => unreachable!(),
        }
    }

    /// Apply the given list of AST arguments to the given definition
    /// parameters, checking that the lengths match in the process.
    ///
    /// If successful, returns the [`DefArgsId`] that represents the arguments.
    ///
    /// Otherwise, returns an error.
    pub(super) fn apply_ast_args_to_def_params(
        &self,
        def_params: DefParamsId,
        args: &[AstArgGroup],
    ) -> TcResult<ResolvedDefArgs> {
        // @@Todo: implicit args
        // @@Todo: default params

        // First ensure that the number of parameter and argument groups match.
        let created_def_args = self.make_def_args_from_ast_arg_groups(args, def_params)?;
        if def_params.len() != created_def_args.len() {
            return Err(TcError::WrongDefArgLength {
                def_params_id: def_params,
                def_args_id: created_def_args.into(),
            });
        }

        // Then ensure that the number of parameters and arguments in each group
        // match.
        let mut errors: Vec<TcError> = vec![];
        for (param_group_index, arg_group_index) in
            def_params.to_index_range().zip(created_def_args.to_index_range())
        {
            let def_param_group =
                self.stores().def_params().get_element((def_params, param_group_index));

            let def_arg_group = match created_def_args {
                ResolvedDefArgs::Term(args) => ResolvedArgs::Term(
                    self.stores().def_args().get_element((args, arg_group_index)).args,
                ),
                ResolvedDefArgs::Pat(args) => {
                    let element = self.stores().def_pat_args().get_element((args, arg_group_index));
                    ResolvedArgs::Pat(element.pat_args, element.spread)
                }
            };

            if def_param_group.params.len() != def_arg_group.len() {
                // Collect errors and only report at the end.
                errors.push(TcError::WrongArgLength {
                    params_id: def_param_group.params,
                    args_id: def_arg_group.into(),
                });
            }
        }
        if !errors.is_empty() {
            return Err(TcError::Compound { errors });
        }

        Ok(created_def_args)
    }
}
