use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::{HasContext, ScopeKind},
    tir::{NodeId, Param, PatId, TermId, TuplePat, TupleTerm, TupleTy, Ty, TyId},
    visitor::Map,
};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult},
    options::normalisation::{normalise_nested, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, ScopedOperationsOnNode},
};

impl<E: TcEnv> OperationsOn<TupleTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        tuple_term: &mut TupleTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let params = match *annotation_ty.value() {
                Ty::TupleTy(tuple_ty) => self.visitor().copy(tuple_ty.data),
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
            self.check_node_scoped(tuple_term.data, params, |new_args| {
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
            self.substituter().apply_sub_from_context(annotation_ty);
            Ok(())
        })
    }

    fn try_normalise(
        &self,
        _item: TupleTerm,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut TupleTerm,
        target: &mut TupleTerm,
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes_scoped(src.data, target.data, |_| Ok(()))
    }
}

impl<E: TcEnv> OperationsOn<TupleTy> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        tuple_ty: &mut TupleTy,
        annotation_ty: Self::AnnotNode,
        _original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.check_node_scoped(tuple_ty.data, (), |()| Ok(()))?;
        self.check_is_universe(annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: TupleTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TyId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut TupleTy,
        target: &mut TupleTy,
        _: Self::Node,
        _: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes_scoped(src.data, target.data, |_| Ok(()))
    }
}

impl<E: TcEnv> OperationsOn<TuplePat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        tuple_pat: &mut TuplePat,
        annotation_ty: Self::AnnotNode,
        original_pat_id: Self::Node,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let params = match *annotation_ty.value() {
            Ty::TupleTy(tuple_ty) => tuple_ty.data,
            Ty::Hole(_) => Param::seq_from_args_with_hole_types(tuple_pat.data),
            _ => {
                let inferred = Param::seq_from_args_with_hole_types(tuple_pat.data);
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::expect_is(
                        original_pat_id,
                        Ty::from(TupleTy { data: inferred }, original_pat_id.origin().inferred()),
                    ),
                });
            }
        };
        let mut tuple_pat = *tuple_pat;
        self.check_node_scoped((tuple_pat.data, tuple_pat.data_spread), params, |new_args| {
            tuple_pat.data = new_args;
            original_pat_id.set(original_pat_id.value().with_data(tuple_pat.into()));
            Ok(())
        })?;

        let tuple_ty = Ty::expect_is(
            original_pat_id,
            Ty::from(TupleTy { data: params }, annotation_ty.origin()),
        );
        self.check_by_unify(tuple_ty, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: TuplePat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<PatId>> {
        normalise_nested()
    }

    fn unify(
        &self,
        _src: &mut TuplePat,
        _target: &mut TuplePat,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        // @@Todo: unification of tuple patterns
        self.mismatching_atoms(src_node, target_node)
    }
}
