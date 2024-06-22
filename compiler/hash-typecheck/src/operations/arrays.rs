use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    intrinsics::{
        definitions::{array_ty, list_ty, usize_ty},
        utils::{create_term_from_usize_lit, try_use_term_as_machine_integer},
    },
    tir::{
        ArgsId, ArrayTerm, DataDefCtors, IndexTerm, NodeId, NodeOrigin, NodesId, ParamIndex,
        PrimitiveCtorInfo, Term, TermId, Ty, TyId,
    },
    visitor::Map,
};

use crate::{
    diagnostics::{TcError, TcResult, WrongTermKind},
    env::{HasTcEnv, TcEnv},
    options::normalisation::{
        normalise_nested, normalised_if, stuck_normalising, NormalisationState, NormaliseResult,
    },
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode, ScopedOperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    /// Get the parameter at the given index in the given argument list.
    pub fn get_param_in_args(&self, args: ArgsId, target: ParamIndex) -> TermId {
        for arg_i in args.iter() {
            let arg = arg_i.value();
            if arg.target == target || ParamIndex::Position(arg_i.1) == target {
                return arg.value;
            }
        }
        panic!("Out of bounds index for access: {}", target)
    }

    /// Set the parameter at the given index in the given argument list.
    pub fn set_param_in_args(&self, args: ArgsId, target: ParamIndex, value: TermId) {
        for arg_i in args.iter() {
            let arg = arg_i.value();
            if arg.target == target || ParamIndex::Position(arg_i.1) == target {
                arg_i.borrow_mut().value = value;
                return;
            }
        }
        panic!("Out of bounds index for access: {}", target)
    }

    /// Get the term at the given index in the given arguments.
    ///
    /// Assumes that the index is normalised.
    pub fn get_index_in_array(&self, elements: ArgsId, index: TermId) -> Option<TermId> {
        try_use_term_as_machine_integer(self, index)
            .map(|idx| elements.elements().at(idx).unwrap().borrow().value)
    }

    /// Get the term at the given index in the given repeated array. If the
    /// index term is larger than the `repeat` count, we fail, otherwise
    /// return the `subject`.
    ///
    /// Assumes that the index is normalised.
    fn get_index_in_repeat(
        &self,
        subject: TermId,
        repeat: TermId,
        index: TermId,
    ) -> Option<TermId> {
        let subject = try_use_term_as_machine_integer(self, subject)?;
        let index = try_use_term_as_machine_integer(self, index)?;

        if index >= subject {
            None
        } else {
            Some(repeat)
        }
    }

    fn use_ty_as_array_ty(&self, annotation_ty: TyId) -> TcResult<Option<(TyId, Option<TermId>)>> {
        let mismatch = || {
            Err(TcError::MismatchingTypes {
                expected: annotation_ty,
                actual: list_ty(Term::fresh_hole(NodeOrigin::Expected), NodeOrigin::Expected),
            })
        };

        match *annotation_ty.value() {
            Ty::DataTy(data) => {
                let data_def = data.data_def.value();

                match data_def.ctors {
                    DataDefCtors::Primitive(primitive) => {
                        if let PrimitiveCtorInfo::Array(array_prim) = primitive {
                            // First infer the data arguments
                            let copied_params = self.visitor().copy(data_def.params);
                            self.check_node(data.args, copied_params)?;
                            let sub = self.substituter().create_sub_from_args_of_params(data.args, copied_params);
                            let subbed_element_ty = self.substituter().apply_sub(array_prim.element_ty, &sub);
                            let subbed_index = array_prim
                                .length
                                .map(|l| self.substituter().apply_sub(l, &sub));
                            Ok(Some((subbed_element_ty, subbed_index)))
                        } else {
                            mismatch()
                        }
                    }
                    _ => mismatch(),
                }
            }
            Ty::Meta(_) => Ok(None),
            _ => mismatch(),
        }
    }

    pub fn normalise_array_term_len(&self, array: ArrayTerm) -> NormaliseResult<usize> {
        match array {
            ArrayTerm::Normal(elements) => Ok(Some(elements.len())),
            ArrayTerm::Repeated(_, repeat) => {
                let term = self.normalise_node_fully(repeat)?;
                let Some(length) = try_use_term_as_machine_integer(self, term) else {
                    return stuck_normalising();
                };
                Ok(Some(length))
            }
        }
    }
}

impl<E: TcEnv> OperationsOn<ArrayTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        array_term: &mut ArrayTerm,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> TcResult<()> {
        let array_len_origin = array_term.length_origin();
        let (inner_ty, array_len) = self
            .use_ty_as_array_ty(annotation_ty)?
            .unwrap_or_else(|| (self.fresh_meta(array_len_origin.inferred()), None));

        // Now unify that the terms that are specified in the array match the
        // annotation type.
        let inferred_len_term = match *array_term {
            ArrayTerm::Normal(elements) => {
                self.check_unified_args(elements, inner_ty)?;
                create_term_from_usize_lit(self.env(), elements.len(), array_len_origin)
            }
            ArrayTerm::Repeated(term, repeat) => {
                self.check_node(term, inner_ty)?;
                self.check_node(repeat, usize_ty(array_len_origin))?;
                repeat
            }
        };

        // Ensure the array lengths match if given
        if let Some(len) = array_len {
            if !self.nodes_are_equal(len, inferred_len_term) {
                return Err(TcError::MismatchingArrayLengths {
                    expected_len: len,
                    got_len: inferred_len_term,
                });
            }
        }

        // Either create  a default type, or apply a substitution to the annotation
        // type.
        //
        // - If the array kind is "repeated", the default annotation that we use is an
        //   array of the specified length.
        //
        // - Otherwise, we just default to a list type.
        if let Ty::Meta(_) = *annotation_ty.value() {
            let default_annotation = match array_term {
                ArrayTerm::Normal(_) => list_ty(inner_ty, NodeOrigin::Expected),
                ArrayTerm::Repeated(_, repeat) => array_ty(inner_ty, *repeat, NodeOrigin::Expected),
            };

            self.unify_nodes(default_annotation, annotation_ty)?;
        };

        Ok(())
    }

    fn try_normalise(
        &self,
        _item: ArrayTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut ArrayTerm,
        target: &mut ArrayTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        match (src, target) {
            (ArrayTerm::Normal(src), ArrayTerm::Normal(target)) => {
                self.unify_nodes(*src, *target)
            }
            (ArrayTerm::Repeated(src, src_repeat), ArrayTerm::Repeated(target, target_repeat)) => {
                self.unify_nodes(*src, *target)?;
                self.unify_nodes(*src_repeat, *target_repeat)
            }
            _ => self.mismatching_atoms(src_node, target_node),
        }
    }
}

impl<E: TcEnv> OperationsOn<IndexTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        index_term: &mut IndexTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let subject_ty = self.fresh_meta_for(index_term.subject);
        self.check_node(index_term.subject, subject_ty)?;

        // Ensure the index is a usize
        let index_ty =
            Ty::expect_is(index_term.index, usize_ty(index_term.index.origin().inferred()));
        self.check_node(index_term.index, index_ty)?;

        let wrong_subject_ty = || {
            Err(TcError::WrongTerm {
                term: original_term_id,
                inferred_term_ty: subject_ty,
                kind: WrongTermKind::NotAnArray,
            })
        };

        self.normalise_node_in_place_no_signals(subject_ty)?;
        // Ensure that the subject is array-like
        let inferred_ty =
            self.try_or_normalise(subject_ty, |subject_ty, _| match *subject_ty.value() {
                Ty::DataTy(data_ty) => {
                    let data_def = data_ty.data_def.value();
                    if let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array_primitive)) =
                        data_def.ctors
                    {
                        let sub = self
                            .substituter()
                            .create_sub_from_args_of_params(data_ty.args, data_def.params);
                        let array_ty =
                            self.substituter().apply_sub(array_primitive.element_ty, &sub);
                        Ok(array_ty)
                    } else {
                        wrong_subject_ty()
                    }
                }
                _ => wrong_subject_ty(),
            })?;

        self.unify_nodes(inferred_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        mut index_term: IndexTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        let st = NormalisationState::new();
        index_term.subject = self.normalise_node_and_record(index_term.subject, &st)?;

        if let Term::Array(array_term) = *index_term.subject.value() {
            let result = match array_term {
                ArrayTerm::Normal(elements) => self.get_index_in_array(elements, index_term.index),
                ArrayTerm::Repeated(subject, count) => {
                    // Evaluate the count, and the index terms to integers:
                    self.get_index_in_repeat(subject, count, index_term.index)
                }
            };

            // Check if we actually got the index when evaluating:
            let Some(index) = result else { return stuck_normalising() };

            let result = self.normalise_node_and_record(index, &st)?;
            normalised_if(|| result, &st)
        } else {
            stuck_normalising()
        }
    }

    fn unify(
        &self,
        src: &mut IndexTerm,
        target: &mut IndexTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.subject, target.subject)?;
        self.unify_nodes(src.index, target.index)
    }
}
