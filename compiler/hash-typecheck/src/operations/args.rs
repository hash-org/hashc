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
        validate_and_reorder_args_against_params, Arg, ArgsId, Node, NodeId, NodesId, ParamsId,
        Pat, PatArgsId, Spread, SymbolId, Term, TermId, TupleTerm, TyId,
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
}
