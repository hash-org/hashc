use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_tir::{
    context::Context,
    intrinsics::{
        definitions::{array_ty, list_ty, usize_ty},
        utils::create_term_from_usize_lit,
    },
    tir::{ArrayPat, ArrayTerm, NodeOrigin, PatId, TermId, Ty, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<ArrayTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _: &mut Context,
        array_term: &mut ArrayTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> TcResult<()> {
        self.infer_ops().normalise_and_check_ty(annotation_ty)?;

        let array_len_origin = array_term.length_origin();
        let (inner_ty, array_len) = self
            .infer_ops()
            .use_ty_as_array(annotation_ty)?
            .unwrap_or_else(|| (Ty::hole(array_len_origin.inferred()), None));

        // Now unify that the terms that are specified in the array match the
        // annotation type.
        let inferred_len_term = match *array_term {
            ArrayTerm::Normal(elements) => {
                self.infer_ops().infer_unified_term_list(elements, inner_ty)?;
                create_term_from_usize_lit(self.target(), elements.len(), array_len_origin)
            }
            ArrayTerm::Repeated(term, repeat) => {
                self.infer_ops().infer_term(term, inner_ty)?;
                self.infer_ops().infer_term(repeat, usize_ty(array_len_origin))?;
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

            self.infer_ops().check_by_unify(default_annotation, annotation_ty)?
        };

        Ok(())
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: ArrayTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
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

impl<E: TcEnv> Operations<ArrayPat> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        _ctx: &mut Context,
        _item: &mut ArrayPat,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: ArrayPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<PatId> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
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
