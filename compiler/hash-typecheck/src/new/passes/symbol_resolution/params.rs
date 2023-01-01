//! This module contains functionality to resolve AST parameters and arguments
//! to terms.

use std::{iter::empty, ops::Range};

use hash_source::location::Span;
use hash_types::new::{
    args::{ArgData, ArgsId, PatArgsId},
    defs::{DefArgGroupData, DefArgsId, DefParamsId, DefPatArgGroupData, DefPatArgsId},
    environment::env::AccessToEnv,
    fns::FnCallTerm,
    params::ParamTarget,
    pats::Spread,
    terms::{Term, TermId},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey};

use super::{paths::AstArgGroup, SymbolResolutionPass};
use crate::new::{
    diagnostics::{
        error::{TcError, TcResult},
        params::{SomeArgsId, SomeDefArgsId},
    },
    ops::{common::CommonOps, AccessToOps},
    passes::ast_pass::AstPass,
};

/// Resolved arguments.
///
/// These are either term arguments, or pattern arguments.
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

impl<'tc> SymbolResolutionPass<'tc> {
    /// Make [`ResolvedArgs`] from an AST argument group, with holes for all the
    /// arguments.
    ///
    /// This will return either pattern arguments or term arguments, depending
    /// on the kind of the argument group.
    pub(super) fn make_args_from_ast_arg_group(
        &self,
        group: &AstArgGroup,
    ) -> TcResult<ResolvedArgs> {
        match group {
            AstArgGroup::ExplicitArgs(args) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        Ok(ArgData {
                            target: arg
                                .name
                                .as_ref()
                                .map(|name| ParamTarget::Name(name.ident))
                                .unwrap_or_else(|| ParamTarget::Position(i)),
                            value: self.make_term_from_ast_expr(arg.value.ast_ref())?,
                        })
                    })
                    .collect::<TcResult<Vec<_>>>()?;
                Ok(ResolvedArgs::Term(self.param_ops().create_args(args.into_iter())))
            }
            AstArgGroup::ImplicitArgs(args) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        Ok(ArgData {
                            target: arg
                                .name
                                .as_ref()
                                .map(|name| ParamTarget::Name(name.ident))
                                .unwrap_or_else(|| ParamTarget::Position(i)),
                            value: self
                                .new_term(Term::Ty(self.make_ty_from_ast_ty(arg.ty.ast_ref())?)),
                        })
                    })
                    .collect::<TcResult<Vec<_>>>()?;
                Ok(ResolvedArgs::Term(self.param_ops().create_args(args.into_iter())))
            }
            AstArgGroup::ExplicitPatArgs(pat_args, spread) => {
                let spread = self.ast_spread_as_spread(spread)?;
                let args = self.ast_tuple_pat_entries_as_pat_args(pat_args)?;
                Ok(ResolvedArgs::Pat(args, spread))
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
                    Ok(ResolvedDefArgs::Pat(
                        self.param_ops().create_def_pat_args(arg_groups.into_iter()),
                    ))
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
                    Ok(ResolvedDefArgs::Term(
                        self.param_ops().create_def_args(arg_groups.into_iter()),
                    ))
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
