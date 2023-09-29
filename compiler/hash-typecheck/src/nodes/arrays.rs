use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_tir::{
    intrinsics::{
        definitions::{array_ty, list_ty, usize_ty},
        utils::create_term_from_usize_lit,
    },
    tir::{
        ArrayPat, ArrayTerm, DataDefCtors, IndexTerm, NodeId, NodeOrigin, PatId, PrimitiveCtorInfo,
        TermId, Ty, TyId,
    },
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult, WrongTermKind},
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<ArrayTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        array_term: &mut ArrayTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;

        let array_len_origin = array_term.length_origin();
        let (inner_ty, array_len) = self
            .use_ty_as_array(annotation_ty)?
            .unwrap_or_else(|| (Ty::hole(array_len_origin.inferred()), None));

        // Now unify that the terms that are specified in the array match the
        // annotation type.
        let inferred_len_term = match *array_term {
            ArrayTerm::Normal(elements) => {
                self.infer_unified_term_list(elements, inner_ty)?;
                create_term_from_usize_lit(self.target(), elements.len(), array_len_origin)
            }
            ArrayTerm::Repeated(term, repeat) => {
                self.infer_term(term, inner_ty)?;
                self.infer_term(repeat, usize_ty(array_len_origin))?;
                repeat
            }
        };

        // Ensure the array lengths match if given
        if let Some(len) = array_len {
            if !self.uni_ops().terms_are_equal(len, inferred_len_term) {
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

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: ArrayTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut ArrayTerm,
        _target: &mut ArrayTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ArrayTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<ArrayPat> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        _item: &mut ArrayPat,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: ArrayPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<PatId> {
        todo!()
    }

    fn unify(
        &self,

        _opts: &UnificationOptions,
        _src: &mut ArrayPat,
        _target: &mut ArrayPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut ArrayPat) {
        todo!()
    }
}

impl<E: TcEnv> Operations<IndexTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        index_term: &mut IndexTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.check_ty(annotation_ty)?;

        let subject_ty = Ty::hole_for(index_term.subject);
        self.infer_term(index_term.subject, subject_ty)?;
        self.normalise_and_check_ty(subject_ty)?;

        // Ensure the index is a usize
        let index_ty =
            Ty::expect_is(index_term.index, usize_ty(index_term.index.origin().inferred()));
        self.infer_term(index_term.index, index_ty)?;

        let wrong_subject_ty = || {
            Err(TcError::WrongTy {
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
                        .sub_ops()
                        .create_sub_from_args_of_params(data_ty.args, data_def.params);
                    let array_ty = self.sub_ops().apply_sub(array_primitive.element_ty, &sub);
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

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: IndexTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut IndexTerm,
        _target: &mut IndexTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut IndexTerm) {
        todo!()
    }
}
