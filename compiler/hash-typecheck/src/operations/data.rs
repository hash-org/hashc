use std::{collections::HashSet, ops::ControlFlow};

use hash_reporting::diagnostic::ErrorState;
use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    intrinsics::definitions::usize_ty,
    tir::{
        Arg, CtorDefId, CtorTerm, DataDefCtors, DataDefId, DataTy, NodeId, NodeOrigin, PatId,
        PrimitiveCtorInfo, TermId, Ty, TyId,
    },
    visitor::Map,
};

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    options::normalisation::{already_normalised, normalise_nested, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode, ScopedOperationsOnNode},
};

impl<E: TcEnv> OperationsOn<CtorTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        term: &mut CtorTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let mut term = *term;
        let ctor_def_id = term.ctor;
        let data_args = term.data_args;
        let ctor = ctor_def_id.value();
        let data_def = ctor.data_def_id.value();

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let mut annotation_data_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: ctor.data_def_id,
                args: if data.args.len() == 0 {
                    Arg::seq_from_params_as_holes(data_def.params)
                } else {
                    data.args
                },
            },
            Ty::Hole(_) => DataTy {
                data_def: ctor.data_def_id,
                args: Arg::seq_from_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        DataTy { args: data_args, data_def: ctor.data_def_id },
                        original_term_id.origin(),
                    ),
                });
            }
        };

        // Get the data arguments given to the constructor, like Equal<...>::Refl(...)
        //                                                             ^^^ these
        let ctor_data_args = if data_args.len() == 0 {
            Arg::seq_from_params_as_holes(data_def.params)
        } else {
            data_args
        };

        // From the given constructor data args, substitute the constructor params and
        // result arguments. In the process, infer the data args more if
        // possible.
        let copied_params = self.visitor().copy(data_def.params);
        let (inferred_ctor_data_args, subbed_ctor_params, subbed_ctor_result_args) = self
            .check_node_scoped(ctor_data_args, copied_params, |inferred_data_args| {
                let sub = self.substituter().create_sub_from_current_scope();
                let subbed_ctor_params = self.substituter().apply_sub(ctor.params, &sub);
                let subbed_ctor_result_args = self.substituter().apply_sub(ctor.result_args, &sub);
                self.substituter().apply_sub_in_place(inferred_data_args, &sub);
                Ok((inferred_data_args, subbed_ctor_params, subbed_ctor_result_args))
            })?;

        // Infer the constructor arguments from the term, using the substituted
        // parameters. Substitute any results to the constructor arguments, the
        // result arguments of the constructor, and the constructor data
        // arguments.
        let (final_result_args, resulting_sub, binds) = self.check_node_scoped(
            term.ctor_args,
            subbed_ctor_params,
            |inferred_term_ctor_args| {
                let ctor_sub = self.substituter().create_sub_from_current_scope();
                self.substituter().apply_sub_in_place(subbed_ctor_result_args, &ctor_sub);
                self.substituter().apply_sub_in_place(inferred_term_ctor_args, &ctor_sub);
                self.substituter().apply_sub_in_place(inferred_ctor_data_args, &ctor_sub);

                // These arguments might have been updated so we need to set them
                term.data_args = inferred_ctor_data_args;
                term.ctor_args = inferred_term_ctor_args;
                original_term_id.set(original_term_id.value().with_data(term.into()));

                // We are exiting the constructor scope, so we need to hide the binds
                let hidden_ctor_sub =
                    self.substituter().hide_param_binds(ctor.params.iter(), &ctor_sub);
                Ok((subbed_ctor_result_args, hidden_ctor_sub, HashSet::new()))
            },
        )?;

        // Set the annotation data type to the final result arguments, and unify
        // the annotation type with the expected type.
        annotation_data_ty.args = final_result_args;
        let expected_data_ty =
            Ty::expect_is(original_term_id, Ty::from(annotation_data_ty, annotation_ty.origin()));
        self.unification_opts.pat_binds.enter(Some(binds), || {
            self.add_sub_to_scope(&resulting_sub);
            self.unify_nodes(expected_data_ty, annotation_ty)
        })?;

        // Now we gather the final substitution, and apply it to the result
        // arguments, the constructor data arguments, and finally the annotation
        // type.
        let final_sub = self.substituter().create_sub_from_current_scope();
        self.substituter().apply_sub_in_place(subbed_ctor_result_args, &final_sub);
        self.substituter().apply_sub_in_place(inferred_ctor_data_args, &final_sub);
        // Set data args because they might have been updated again
        term.data_args = inferred_ctor_data_args;
        original_term_id.set(original_term_id.value().with_data(term.into()));
        self.substituter().apply_sub_in_place(annotation_ty, &final_sub);

        for (data_arg, result_data_arg) in term.data_args.iter().zip(subbed_ctor_result_args.iter())
        {
            let data_arg = data_arg.value();
            let result_data_arg = result_data_arg.value();
            if let Ty::Hole(_) = *data_arg.value.value() {
                data_arg.value.set(result_data_arg.value.value());
            }
        }

        Ok(())
    }

    fn try_normalise(
        &self,
        _item: CtorTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut CtorTerm,
        target: &mut CtorTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        if src.ctor != target.ctor {
            return self.mismatching_atoms(src_node, target_node);
        }
        self.unify_nodes_scoped(src.data_args, target.data_args, |_| Ok(()))?;
        self.unify_nodes_scoped(src.ctor_args, target.ctor_args, |_| Ok(()))?;
        Ok(())
    }
}

impl<E: TcEnv> OperationsOn<DataTy> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        data_ty: &mut DataTy,
        annotation_ty: Self::AnnotNode,
        term_id: Self::Node,
    ) -> TcResult<()> {
        let data_def = data_ty.data_def.value();
        let copied_params = self.visitor().copy(data_def.params);
        self.check_node_scoped(data_ty.args, copied_params, |inferred_data_ty_args| {
            data_ty.args = inferred_data_ty_args;
            term_id.set(term_id.value().with_data((*data_ty).into()));
            Ok(())
        })?;
        self.check_is_universe(annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: DataTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TyId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut DataTy,
        target: &mut DataTy,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        if src.data_def != target.data_def {
            return self.mismatching_atoms(src_node, target_node);
        }
        self.unify_nodes_scoped(src.args, target.args, |_| Ok(()))
    }
}

impl<E: TcEnv> OperationsOnNode<DataDefId> for Tc<'_, E> {
    type AnnotNode = ();

    fn check_node(&self, data_def_id: DataDefId, _: Self::AnnotNode) -> TcResult<()> {
        let (data_def_params, data_def_ctors) =
            data_def_id.map(|data_def| (data_def.params, data_def.ctors));

        self.check_node_scoped(data_def_params, (), |_| {
            match data_def_ctors {
                DataDefCtors::Defined(data_def_ctors_id) => {
                    let mut error_state = ErrorState::new();

                    // Infer each member
                    for ctor in data_def_ctors_id.value().iter() {
                        let _ = error_state.try_or_add_error(self.check_node(ctor, ()));
                    }

                    error_state.into_error(|| Ok(()))
                }
                DataDefCtors::Primitive(primitive) => {
                    match primitive {
                        PrimitiveCtorInfo::Numeric(_)
                        | PrimitiveCtorInfo::Str
                        | PrimitiveCtorInfo::Char => {
                            // Nothing to do
                            Ok(())
                        }
                        PrimitiveCtorInfo::Array(array_ctor_info) => {
                            // Infer the inner type and length
                            self.check_node(
                                array_ctor_info.element_ty,
                                Ty::universe_of(array_ctor_info.element_ty),
                            )?;
                            if let Some(length) = array_ctor_info.length {
                                self.check_node(length, usize_ty(NodeOrigin::Expected))?;
                            }
                            Ok(())
                        }
                    }
                }
            }
        })
    }

    fn try_normalise_node(&self, _item: DataDefId) -> NormaliseResult<ControlFlow<DataDefId>> {
        already_normalised()
    }

    fn unify_nodes(&self, src: DataDefId, _: DataDefId) -> TcResult<()> {
        // @@Todo: implement unification of definitions
        Err(TcError::Blocked(src.origin()))
    }
}

impl<E: TcEnv> OperationsOnNode<CtorDefId> for Tc<'_, E> {
    type AnnotNode = ();

    fn check_node(&self, ctor: CtorDefId, _: Self::AnnotNode) -> TcResult<()> {
        let ctor_def = ctor.value();
        self.check_node_scoped(ctor_def.params, (), |()| {
            let return_ty = Ty::from(
                DataTy { data_def: ctor_def.data_def_id, args: ctor_def.result_args },
                ctor.origin(),
            );
            self.check_node(return_ty, Ty::universe_of(return_ty))?;
            Ok(())
        })
    }

    fn try_normalise_node(&self, _item: CtorDefId) -> NormaliseResult<ControlFlow<CtorDefId>> {
        already_normalised()
    }

    fn unify_nodes(&self, src: CtorDefId, _target: CtorDefId) -> TcResult<()> {
        // @@Todo: implement unification of definitions
        Err(TcError::Blocked(src.origin()))
    }
}
