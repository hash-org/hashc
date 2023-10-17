//! Typechecking for argument lists and pattern argument lists.
//!
//! These are scoped because the arguments are added into the context for the
//! duration of the check, needed for resolving dependent names in constructors
//! and functions.
// @@DRY: the operations for arguments and pattern arguments are really similar,
// maybe there is a way to abstract both of them into a single operation?
use std::{collections::HashSet, ops::ControlFlow};

use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{HasContext, ScopeKind},
    tir::{
        validate_and_reorder_args_against_params, validate_and_reorder_pat_args_against_params,
        Arg, ArgsId, Node, NodeId, NodesId, ParamsId, Pat, PatArgsId, PatOrCapture, Spread,
        SymbolId, Term, TermId, TupleTerm, TyId,
    },
    visitor::{Atom, Map, Visit},
};
use itertools::Itertools;

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    options::normalisation::{normalise_nested, NormaliseResult, NormaliseSignal},
    tc::Tc,
    traits::{OperationsOnNode, ScopedOperationsOnNode},
    utils::matching::MatchResult,
};

impl<E: TcEnv> ScopedOperationsOnNode<ArgsId> for Tc<'_, E> {
    type AnnotNode = ParamsId;
    type CallbackArg = ArgsId;

    fn check_node_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        args: ArgsId,
        annotation_params: Self::AnnotNode,
        mut in_arg_scope: F,
    ) -> TcResult<T> {
        self.register_new_atom(args, annotation_params);
        // Reorder the arguments to match the annotation parameters:
        let reordered_args_id = validate_and_reorder_args_against_params(args, annotation_params)?;

        let result = self.check_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
                // Check each argument against the corresponding parameter type
                let arg = arg.value();
                self.check_node(arg.value, param_ty)?;
                Ok(())
            },
            |arg| {
                let arg = arg.value();
                Some(arg.value)
            },
            || in_arg_scope(reordered_args_id),
        )?;

        Ok(result)
    }

    fn try_normalise_node(&self, _: ArgsId) -> NormaliseResult<ControlFlow<ArgsId>> {
        // Recurse to the argument values, the argument list itself does not get
        // evaluated to anything
        normalise_nested()
    }

    fn unify_nodes_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        src_id: ArgsId,
        target_id: ArgsId,
        mut f: F,
    ) -> TcResult<T> {
        if src_id.len() != target_id.len() {
            return Err(TcError::DifferentParamOrArgLengths {
                a: src_id.into(),
                b: target_id.into(),
            });
        }
        // Unify each argument individually
        // @@Incomplete: do we not need to take into account dependent references here?
        for (src_arg_id, target_arg_id) in src_id.iter().zip(target_id.iter()) {
            let src_arg = src_arg_id.value();
            let target_arg = target_arg_id.value();
            self.unify_nodes(src_arg.value, target_arg.value)?;
        }
        f(src_id)
    }
}

impl<E: TcEnv> Tc<'_, E> {
    /// Get the pattern bindings in the given pattern arguments.
    pub fn get_binds_in_pat_args(&self, pat_args: PatArgsId) -> HashSet<SymbolId> {
        let mut binds = HashSet::new();
        self.visitor().visit(pat_args, &mut |atom| {
            if let Atom::Pat(pat_id) = atom {
                match *pat_id.value() {
                    Pat::Binding(var) => {
                        binds.insert(var.name);
                        ControlFlow::Break(())
                    }
                    _ => ControlFlow::Continue(()),
                }
            } else {
                ControlFlow::Break(())
            }
        });
        binds
    }
}

/// Pattern arguments might also contain a spread, which is included here.
// @@Cleanup: the spread should probably be part of `PatArgs` rather than
// carried around everywhere else..
impl<E: TcEnv> ScopedOperationsOnNode<(PatArgsId, Option<Spread>)> for Tc<'_, E> {
    type AnnotNode = ParamsId;
    type CallbackArg = PatArgsId;

    fn check_node_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        (pat_args, spread): (PatArgsId, Option<Spread>),
        annotation_params: Self::AnnotNode,
        mut f: F,
    ) -> TcResult<T> {
        self.register_new_atom(pat_args, annotation_params);
        // Reorder the arguments to match the annotation parameters:
        let reordered_pat_args_id =
            validate_and_reorder_pat_args_against_params(pat_args, spread, annotation_params)?;

        self.check_some_args(
            reordered_pat_args_id.iter(),
            annotation_params,
            |pat_arg, param_ty| {
                // Check each argument that isn't a capture, against the
                // corresponding parameter type
                let pat_arg = pat_arg.value();
                match pat_arg.pat {
                    PatOrCapture::Pat(pat) => {
                        self.check_node(pat, (param_ty, None))?;
                        Ok(())
                    }
                    PatOrCapture::Capture(_) => Ok(()),
                }
            },
            |arg| {
                // For arguments that aren't captures, we might be able to use
                // them as terms:
                let arg = arg.value();
                match arg.pat {
                    PatOrCapture::Pat(pat) => pat.try_use_as_term(),
                    PatOrCapture::Capture(_) => None,
                }
            },
            || f(reordered_pat_args_id),
        )
    }

    fn try_normalise_node(
        &self,
        _item: (PatArgsId, Option<Spread>),
    ) -> NormaliseResult<ControlFlow<(PatArgsId, Option<Spread>)>> {
        normalise_nested()
    }

    fn unify_nodes_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        (pat_args_id, _): (PatArgsId, Option<Spread>),
        _: (PatArgsId, Option<Spread>),
        _f: F,
    ) -> TcResult<T> {
        // @@Todo
        Err(TcError::Blocked(pat_args_id.origin()))
    }
}

impl<E: TcEnv> Tc<'_, E> {
    /// Infer and check the given arguments (specialised
    /// for args and pat args below).
    ///
    /// Assumes that they are validated against one another
    pub fn check_some_args<U, Arg: Clone>(
        &self,
        args: impl Iterator<Item = Arg>,
        annotation_params: ParamsId,
        infer_arg: impl Fn(&Arg, TyId) -> TcResult<()>,
        get_arg_value: impl Fn(&Arg) -> Option<TermId>,
        in_arg_scope: impl FnOnce() -> TcResult<U>,
    ) -> TcResult<U> {
        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for (arg, param_id) in args.zip(annotation_params.iter()) {
                    let param = param_id.value();
                    let param_ty = self.visitor().copy(param.ty);
                    infer_arg(&arg, param_ty)?;
                    self.substituter().apply_sub_from_context(param_ty);
                    if let Some(value) = get_arg_value(&arg) {
                        self.context().add_assignment(param.name, param_ty, value);
                    }
                }
                let result = in_arg_scope()?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.substituter().create_sub_from_current_scope();
                let shadowed_sub =
                    self.substituter().hide_param_binds(annotation_params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.add_sub_to_scope(&shadowed_sub);
        Ok(result)
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_args(&self, term_args: ArgsId, pat_args: PatArgsId) -> ArgsId {
        // Create a new tuple term with the spread elements
        let spread_term_args = pat_args
            .elements()
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p.pat {
                PatOrCapture::Pat(_) => None,
                PatOrCapture::Capture(_) => {
                    let arg = term_args.at(i).unwrap().value();
                    Some(Node::at(Arg { target: arg.target, value: arg.value }, arg.origin))
                }
            })
            .collect_vec();

        Node::create_at(Node::<Arg>::seq(spread_term_args), term_args.origin().computed())
    }

    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    pub fn match_args_and_get_binds(
        &self,
        term_args: ArgsId,
        pat_args: PatArgsId,
        spread: Option<Spread>,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        self.match_some_sequence_and_get_binds(
            term_args.len(),
            spread,
            |sp| {
                Term::from(
                    TupleTerm { data: self.extract_spread_args(term_args, pat_args) },
                    sp.name.origin().computed(),
                )
            },
            |i| pat_args.at(i).unwrap().borrow().pat,
            |i| term_args.at(i).unwrap().borrow().value,
            f,
        )
    }
}
