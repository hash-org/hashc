use std::ops::ControlFlow;

use hash_reporting::diagnostic::ErrorState;
use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    context::{HasContext, ScopeKind},
    intrinsics::definitions::usize_ty,
    tir::{
        CtorDefId, CtorTerm, DataDefCtors, DataDefId, DataTy, NodeId, NodeOrigin,
        PrimitiveCtorInfo, Term, TermId, Ty, TyId,
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
        let ctor = ctor_def_id.value();
        let data_def = ctor.data_def_id.value();
        let hole_args = self.args_from_params_as_holes(data_def.params);

        let copied_ctor_params = self.visitor().copy(ctor.params);
        let copied_ctor_result_args = self.visitor().copy(ctor.result_args);

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let annotation_data_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: ctor.data_def_id,
                args: if data.args.len() == 0 { hole_args } else { self.visitor().copy(data.args) },
            },
            Ty::Meta(_) => DataTy {
                data_def: ctor.data_def_id,
                args: self.args_from_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        DataTy { args: hole_args, data_def: ctor.data_def_id },
                        original_term_id.origin(),
                    ),
                });
            }
        };

        // Infer the constructor arguments from the term, using the substituted
        // parameters. Substitute any results to the constructor arguments, the
        // result arguments of the constructor, and the constructor data
        // arguments.
        self.context().enter_scope(ScopeKind::Sub, || {
            self.check_node_scoped(term.ctor_args, copied_ctor_params, |inferred_term_ctor_args| {
                term.ctor_args = inferred_term_ctor_args;
                original_term_id.set(original_term_id.value().with_data(term.into()));

                self.substituter().apply_sub_from_context(copied_ctor_params);
                self.unify_nodes_scoped(copied_ctor_result_args, annotation_data_ty.args, |_| {
                    Ok(())
                })?;

                annotation_ty
                    .set(annotation_ty.value().with_data(Term::DataTy(annotation_data_ty)));
                Ok(())
            })
        })
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
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.ctor, target.ctor)?;
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

    fn try_normalise(&self, _: DataTy, _: Self::Node) -> NormaliseResult<ControlFlow<TyId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut DataTy,
        target: &mut DataTy,
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.data_def, target.data_def)?;
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

    fn unify_nodes(&self, src: DataDefId, target: DataDefId) -> TcResult<()> {
        if src == target {
            Ok(())
        } else {
            Err(TcError::MismatchingDataDefs { expected: src, actual: target })
        }
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

    fn unify_nodes(&self, src: CtorDefId, target: CtorDefId) -> TcResult<()> {
        if src == target {
            Ok(())
        } else {
            Err(TcError::MismatchingCtorDefs { expected: src, actual: target })
        }
    }
}
