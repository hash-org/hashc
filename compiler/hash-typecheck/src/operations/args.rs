//! Typechecking for argument lists and pattern argument lists.
//!
//! These are scoped because the arguments are added into the context for the
//! duration of the check, needed for resolving dependent names in constructors
//! and functions.
// @@DRY: the operations for arguments and pattern arguments are really similar,
// maybe there is a way to abstract both of them into a single operation?
use std::ops::ControlFlow;

use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{HasContext, ScopeKind},
    sub::Sub,
    tir::{
        validate_and_reorder_args_against_params, Arg, ArgsId, Node, NodeId, ParamsId, PatArgsId,
        SymbolId, TermId,
    },
    visitor::Map,
};

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

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                let mut running_sub = Sub::identity();

                for (arg, param_id) in args.iter().zip(annotation_params.iter()) {
                    let param = param_id.value();
                    let param_ty = self.visitor().copy(param.ty);
                    self.substituter().apply_sub_in_place(param_ty, &running_sub);
                    println!("args {}", args);
                    println!("running_sub: {:?}", running_sub);

                    // @@Todo: fix this mess

                    // Check each argument against the corresponding parameter type
                    let arg = arg.value();
                    self.check_node(arg.value, param_ty)?;

                    if self.has_effects(arg.value) == Some(false)
                        && let Some(value) = arg.value.use_as_non_pat()
                    {
                        running_sub.insert(param.name, value);
                    }
                }
                let result = in_arg_scope(reordered_args_id)?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.substituter().create_sub_from_current_scope();
                let shadowed_sub =
                    self.substituter().hide_param_binds(annotation_params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.context().add_sub_to_scope(&shadowed_sub);

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
        for (src_arg_id, target_arg_id) in src_id.iter().zip(target_id.iter()) {
            let src_arg = src_arg_id.value();
            let target_arg = target_arg_id.value();
            self.unify_nodes(src_arg.value, target_arg.value)?;
        }
        f(src_id)
    }
}

impl<E: TcEnv> Tc<'_, E> {
    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn _extract_spread_args(&self, term_args: ArgsId, pat_args: ArgsId) -> ArgsId {
        debug_assert!(pat_args.len() <= term_args.len());

        let pat_arg_spread_idx = pat_args.get_spread_idx();
        if pat_arg_spread_idx.is_none() {
            return ArgsId::empty();
        }

        let spread_args = term_args
            .iter()
            .skip(pat_arg_spread_idx.unwrap())
            .take(pat_args.len() - pat_arg_spread_idx.unwrap())
            .map(|arg| arg.value())
            .collect::<Vec<_>>();

        Node::create_at(Node::<Arg>::seq(spread_args), pat_args.origin().computed())
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
        // @@Todo: restore spread handling
        // spread: Option<Spread>,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        self.match_some_sequence_and_get_binds(
            term_args.len(),
            // spread,
            // |sp| {
            //     Term::from(
            //         TupleTerm { data: self.extract_spread_args(term_args, pat_args) },
            //         sp.name.origin().computed(),
            //     )
            // },
            |i| pat_args.at(i).unwrap().borrow().value,
            |i| term_args.at(i).unwrap().borrow().value,
            f,
        )
    }
}
