use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::{HasContext, ScopeKind},
    tir::{NodeId, Param, TermId, TupleTerm, TupleTy, Ty, TyId},
    visitor::{Map, Visitor},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<TupleTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        tuple_term: &mut TupleTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let params = match *annotation_ty.value() {
                Ty::TupleTy(tuple_ty) => Visitor::new().copy(tuple_ty.data),
                Ty::Hole(_) => Param::seq_from_args_with_hole_types(tuple_term.data),
                _ => {
                    let inferred = Param::seq_from_args_with_hole_types(tuple_term.data);
                    return Err(TcError::MismatchingTypes {
                        expected: annotation_ty,
                        actual: Ty::from(
                            TupleTy { data: inferred },
                            original_term_id.origin().inferred(),
                        ),
                    });
                }
            };

            let mut tuple_term = *tuple_term;
            self.infer_args(tuple_term.data, params, |new_args| {
                tuple_term.data = new_args;
                original_term_id.set(original_term_id.value().with_data(tuple_term.into()));
                Ok(())
            })?;

            let tuple_ty = Ty::expect_is(
                original_term_id,
                Ty::from(TupleTy { data: params }, annotation_ty.origin()),
            );
            self.check_by_unify(tuple_ty, annotation_ty)?;
            // @@Review: why is this needed? Shouldn't the substitution be applied during
            // `check_by_unify`?
            self.sub_ops().apply_sub_from_context(annotation_ty);
            Ok(())
        })
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: TupleTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut TupleTerm,
        _target: &mut TupleTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TupleTerm) {
        todo!()
    }
}

impl<E: TcEnv> Operations<TupleTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _item: &mut TupleTy,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: TupleTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<TyId> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut TupleTy,
        _target: &mut TupleTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut TupleTy) {
        todo!()
    }
}
