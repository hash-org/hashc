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
        Arg, ArgsId, Node, NodeId, ParamsId, Pat, PatArgsId, PatOrCapture, Spread, SymbolId,
        TermId, TyId,
    },
    visitor::{Atom, Map, Visit},
};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult},
    options::normalisation::{normalised_if, NormalisationState, NormaliseResult, NormaliseSignal},
    tc::Tc,
    utils::operation_traits::{OperationsOnNode, RecursiveOperationsOnNode},
};

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
        self.add_unification_from_sub(&shadowed_sub);
        Ok(result)
    }
}

impl<E: TcEnv> RecursiveOperationsOnNode<ArgsId> for Tc<'_, E> {
    type TyNode = ParamsId;
    type RecursiveArg = ArgsId;

    fn check_node_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,

        args: ArgsId,
        annotation_params: Self::TyNode,
        mut in_arg_scope: F,
    ) -> TcResult<T> {
        self.register_new_atom(args, annotation_params);
        let reordered_args_id = validate_and_reorder_args_against_params(args, annotation_params)?;

        let result = self.check_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
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

    fn normalise_node(&self, args_id: ArgsId) -> NormaliseResult<ArgsId> {
        let args = args_id.value();
        let st = NormalisationState::new();

        let evaluated_arg_data = args
            .value()
            .into_iter()
            .map(|arg| -> Result<_, NormaliseSignal> {
                Ok(Node::at(
                    Arg {
                        target: arg.target,
                        value: (self.eval_nested_and_record(arg.value.into(), &st)?).to_term(),
                    },
                    arg.origin,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let new_node =
            Node::create_at(Node::<Arg>::seq(evaluated_arg_data), args_id.origin().computed());

        normalised_if(|| new_node, &st)
    }

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
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
        for (src_arg_id, target_arg_id) in src_id.iter().zip(target_id.iter()) {
            let src_arg = src_arg_id.value();
            let target_arg = target_arg_id.value();
            self.unify_nodes(src_arg.value, target_arg.value)?;
        }
        f(src_id)
    }

    fn substitute_node_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: ArgsId,
        _f: F,
    ) -> T {
        todo!()
    }
}

impl<E: TcEnv> Tc<'_, E> {
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

impl<E: TcEnv> RecursiveOperationsOnNode<(PatArgsId, Option<Spread>)> for Tc<'_, E> {
    type TyNode = ParamsId;
    type RecursiveArg = PatArgsId;

    fn check_node_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        (pat_args, spread): (PatArgsId, Option<Spread>),
        annotation_params: Self::TyNode,
        mut f: F,
    ) -> TcResult<T> {
        self.register_new_atom(pat_args, annotation_params);
        let reordered_pat_args_id =
            validate_and_reorder_pat_args_against_params(pat_args, spread, annotation_params)?;

        self.check_some_args(
            reordered_pat_args_id.iter(),
            annotation_params,
            |pat_arg, param_ty| {
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
                let arg = arg.value();
                match arg.pat {
                    PatOrCapture::Pat(pat) => pat.try_use_as_term(),
                    PatOrCapture::Capture(_) => None,
                }
            },
            || f(reordered_pat_args_id),
        )
    }

    fn normalise_node(
        &self,

        _item: (PatArgsId, Option<Spread>),
    ) -> NormaliseResult<(PatArgsId, Option<Spread>)> {
        todo!()
    }

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,

        _src: (PatArgsId, Option<Spread>),
        _target: (PatArgsId, Option<Spread>),
        _f: F,
    ) -> TcResult<T> {
        todo!()
    }

    fn substitute_node_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: (PatArgsId, Option<Spread>),
        _f: F,
    ) -> T {
        todo!()
    }
}
