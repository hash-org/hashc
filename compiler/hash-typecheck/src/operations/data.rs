use std::ops::ControlFlow;

use hash_reporting::diagnostic::ErrorState;
use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    context::{HasContext, ScopeKind},
    intrinsics::definitions::usize_ty,
    tir::{
        CtorDefId, CtorTerm, DataDefCtors, DataDefId, DataTy, FnTy, Node, NodeId, NodeOrigin,
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

impl<E: TcEnv> Tc<'_, E> {
    pub(crate) fn get_fn_ty_for_ctor(&self, ctor: CtorDefId, origin: NodeOrigin) -> TermId {
        let ctor = ctor.value();
        let data_def = ctor.data_def_id.value();
        let res = self.params_and_ret_to_fn_ty(
            [(data_def.params, true), (ctor.params, false)],
            Ty::from(DataTy { args: ctor.result_args, data_def: ctor.data_def_id }, origin),
        );
        res
    }

    pub(crate) fn get_fn_ty_for_data(&self, data: DataDefId, origin: NodeOrigin) -> TermId {
        let data_def = data.value();
        self.params_and_ret_to_fn_ty([(data_def.params, true)], Ty::universe(origin))
    }
}

impl<E: TcEnv> OperationsOn<CtorTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        term: &mut CtorTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let fn_ty = self.get_fn_ty_for_ctor(term.ctor, original_term_id.origin());

        match term.data_ty_args {
            Some(data_ty_args) => {
                let subject_ty = self.fresh_meta_for(original_term_id);
                match self.check_args_against_fn_ty(
                    fn_ty,
                    data_ty_args,
                    true,
                    subject_ty,
                    original_term_id, // @@Fixme: this is not the right originator
                )? {
                    Some(_) => unreachable!(),
                    None => {
                        match self.check_args_against_fn_ty(
                            subject_ty,
                            term.ctor_args,
                            false,
                            annotation_ty,
                            original_term_id,
                        )? {
                            Some(_) => unreachable!(),
                            None => Ok(()),
                        }
                    }
                }
            }
            None => {
                match self.check_args_against_fn_ty(
                    fn_ty,
                    term.ctor_args,
                    false,
                    annotation_ty,
                    original_term_id,
                )? {
                    Some(inserted_args) => {
                        term.data_ty_args = Some(inserted_args);
                        self.check(term, annotation_ty, original_term_id)
                    }
                    None => Ok(()),
                }
            }
        }
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
        self.unify_nodes(src.ctor_args, target.ctor_args)?;
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
        let fn_ty = self.get_fn_ty_for_data(data_ty.data_def, term_id.origin());
        match self.check_args_against_fn_ty(fn_ty, data_ty.args, true, annotation_ty, term_id)? {
            Some(_) => unreachable!(), // @@Fixme: this might occur
            None => Ok(()),
        }
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
        self.unify_nodes(src.args, target.args)
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
        if src == target || src.borrow().ctors.len() == 0 || target.borrow().ctors.len() == 0 {
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
