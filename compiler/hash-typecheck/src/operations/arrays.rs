use std::ops::ControlFlow;

use hash_storage::store::{
    SequenceStoreKey, TrivialSequenceStoreKey,
    statics::{SequenceStoreValue, StoreId},
};
use hash_tir::{
    intrinsics::{
        definitions::{array_ty, list_def, list_ty, usize_ty},
        utils::{create_term_from_usize_lit, try_use_term_as_machine_integer},
    },
    tir::{
        ArgsId, ArrayPat, ArrayTerm, DataDefCtors, IndexTerm, Node, NodeId, NodeOrigin, NodesId,
        ParamIndex, PatId, PatListId, PatOrCapture, PrimitiveCtorInfo, Term, TermId, TermListId,
        Ty, TyId,
    },
    visitor::Map,
};
use itertools::Itertools;

use crate::{
    diagnostics::{TcError, TcResult, WrongTermKind},
    env::{HasTcEnv, TcEnv},
    options::normalisation::{
        NormalisationState, NormaliseResult, normalise_nested, normalised_if, stuck_normalising,
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

    /// Get the term at the given index in the given term list.
    ///
    /// Assumes that the index is normalised.
    pub fn get_index_in_array(&self, elements: TermListId, index: TermId) -> Option<TermId> {
        try_use_term_as_machine_integer(self, index).map(|idx| elements.elements().at(idx).unwrap())
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

        if index >= subject { None } else { Some(repeat) }
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    pub fn extract_spread_list(&self, array_term: ArrayTerm, array_pat: PatListId) -> TermListId {
        // Create a new list term with the spread elements
        let spread_term_list = array_pat
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p {
                PatOrCapture::Pat(_) => None,
                PatOrCapture::Capture(_) => Some(array_term.element_at(i).unwrap()),
            })
            .collect_vec();
        Node::create_at(TermId::seq(spread_term_list), array_term.length_origin().computed())
    }

    fn use_ty_as_array_ty(&self, annotation_ty: TyId) -> TcResult<Option<(TyId, Option<TermId>)>> {
        let mismatch = || {
            Err(TcError::MismatchingTypes {
                expected: annotation_ty,
                actual: list_ty(Ty::hole(NodeOrigin::Expected), NodeOrigin::Expected),
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
                            self.check_node_scoped(data.args, copied_params, |_| {
                                let sub = self.substituter().create_sub_from_current_scope();
                                let subbed_element_ty =
                                    self.substituter().apply_sub(array_prim.element_ty, &sub);
                                let subbed_index = array_prim
                                    .length
                                    .map(|l| self.substituter().apply_sub(l, &sub));
                                Ok(Some((subbed_element_ty, subbed_index)))
                            })
                        } else {
                            mismatch()
                        }
                    }
                    _ => mismatch(),
                }
            }
            Ty::Hole(_) => Ok(None),
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
        self.normalise_and_check_ty(annotation_ty)?;

        let array_len_origin = array_term.length_origin();
        let (inner_ty, array_len) = self
            .use_ty_as_array_ty(annotation_ty)?
            .unwrap_or_else(|| (Ty::hole(array_len_origin.inferred()), None));

        // Now unify that the terms that are specified in the array match the
        // annotation type.
        let inferred_len_term = match *array_term {
            ArrayTerm::Normal(elements) => {
                self.check_unified_term_list(elements, inner_ty)?;
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
        if let Ty::Hole(_) = *annotation_ty.value() {
            let default_annotation = match array_term {
                ArrayTerm::Normal(_) => list_ty(inner_ty, NodeOrigin::Expected),
                ArrayTerm::Repeated(_, repeat) => array_ty(inner_ty, *repeat, NodeOrigin::Expected),
            };

            self.check_by_unify(default_annotation, annotation_ty)?
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
        _src: &mut ArrayTerm,
        _target: &mut ArrayTerm,
        src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        // @@Todo
        Err(TcError::Blocked(src_node.origin()))
    }
}

impl<E: TcEnv> OperationsOn<ArrayPat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        list_pat: &mut ArrayPat,
        annotation_ty: Self::AnnotNode,
        original_pat_id: Self::Node,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        // @@Todo: `use_ty_as_array` instead of this manual match:
        let list_annotation_inner_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == list_def() => {
                // Type is already checked
                assert!(data.args.len() == 1);
                data.args.at(0).unwrap().borrow().value
            }
            Ty::Hole(_) => Ty::hole(list_pat.pats.origin()),
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: list_ty(
                        Ty::hole(NodeOrigin::Generated),
                        original_pat_id.origin().inferred(),
                    ),
                });
            }
        };

        self.check_unified_pat_list(list_pat.pats, list_annotation_inner_ty)?;
        let list_ty = list_ty(list_annotation_inner_ty, NodeOrigin::Expected);
        self.check_by_unify(list_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: ArrayPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<PatId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        _src: &mut ArrayPat,
        _target: &mut ArrayPat,
        src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        // @@Todo
        Err(TcError::Blocked(src_node.origin()))
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
        self.check_ty(annotation_ty)?;

        let subject_ty = Ty::hole_for(index_term.subject);
        self.check_node(index_term.subject, subject_ty)?;
        self.normalise_and_check_ty(subject_ty)?;

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

        // Ensure that the subject is array-like
        let inferred_ty = match *subject_ty.value() {
            Ty::DataTy(data_ty) => {
                let data_def = data_ty.data_def.value();
                if let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array_primitive)) =
                    data_def.ctors
                {
                    let sub = self
                        .substituter()
                        .create_sub_from_args_of_params(data_ty.args, data_def.params);
                    let array_ty = self.substituter().apply_sub(array_primitive.element_ty, &sub);
                    Ok(array_ty)
                } else {
                    wrong_subject_ty()
                }
            }
            _ => wrong_subject_ty(),
        }?;

        self.check_by_unify(inferred_ty, annotation_ty)?;
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
