use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{Context, ScopeKind},
    tir::{FnDefId, FnTy, NodeId, NodeOrigin, Term, TermId, Ty, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    inference::FnInferMode,
    operations::{
        checking::{already_checked, did_check, CheckResult, CheckState},
        normalisation::{already_normalised, NormaliseResult},
        unification::{UnifyResult, UnifySignal},
        Operations,
    },
};

impl<E: TcEnv> Operations<FnTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _: &mut Context,
        fn_ty: &mut FnTy,
        item_ty: Self::TyNode,
        _: Self::Node,
    ) -> CheckResult {
        let state = CheckState::new();
        state.then(self.check_is_universe(item_ty))?;
        self.infer_ops().infer_params(fn_ty.params, || {
            self.infer_ops().infer_term(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
        })?;
        state.done()
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut FnTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        already_normalised()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        f1: &mut FnTy,
        f2: &mut FnTy,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> UnifyResult {
        if !self.uni_ops().fn_modalities_match(*f1, *f2) {
            self.uni_ops().mismatching_atoms(src_id, target_id)?;
            Ok(())
        } else {
            // Unify parameters and apply to return types
            self.uni_ops().unify_params(f1.params, f2.params, || {
                self.uni_ops().unify_terms(f1.return_ty, f2.return_ty)
            })?;

            let forward_sub = self.sub_ops().create_sub_from_param_names(f1.params, f2.params);
            f2.return_ty = self.sub_ops().apply_sub(f2.return_ty, &forward_sub);

            let backward_sub = self.sub_ops().create_sub_from_param_names(f2.params, f1.params);
            f1.return_ty = self.sub_ops().apply_sub(f1.return_ty, &backward_sub);

            src_id.set(src_id.value().with_data((*f1).into()));
            target_id.set(target_id.value().with_data((*f2).into()));

            Ok(())
        }
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut FnTy) {
        todo!()
    }
}

impl<E: TcEnv> Operations<(FnDefId, FnInferMode)> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _: &mut Context,
        fn_def_id: &mut (FnDefId, FnInferMode),
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> CheckResult {
        let (fn_def_id, fn_mode) = *fn_def_id;
        self.infer_ops().check_ty(annotation_ty)?;
        if let Some(fn_ty) = self.infer_ops().try_get_inferred_ty(fn_def_id) {
            let expected =
                Ty::expect_is(original_term_id, Ty::from(fn_ty, fn_def_id.origin().inferred()));
            self.infer_ops().check_by_unify(expected, annotation_ty)?;
            return did_check(());
        }

        self.infer_ops().infer_fn_annotation_ty(fn_def_id, annotation_ty)?;
        let fn_def = fn_def_id.value();

        if fn_mode == FnInferMode::Header {
            // If we are only inferring the header, then we also want to check for
            // immediate body functions.
            self.infer_ops().infer_params(fn_def.ty.params, || {
                self.infer_ops()
                    .infer_term(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                if let Term::Fn(immediate_body_fn) = *fn_def.body.value() {
                    self.infer_ops().infer_fn_def(
                        immediate_body_fn,
                        Ty::hole_for(fn_def.body),
                        fn_def.body,
                        FnInferMode::Header,
                    )?;
                }
                Ok(())
            })?;
            return did_check(());
        }

        if self.atom_is_registered(fn_def_id) {
            // Recursive call
            return already_checked(());
        }

        self.register_new_atom(fn_def_id, fn_def.ty);

        let fn_def = fn_def_id.value();

        self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
            self.infer_ops().infer_params(fn_def.ty.params, || {
                self.infer_ops()
                    .infer_term(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                self.infer_ops().infer_term(fn_def.body, fn_def.ty.return_ty)
            })
        })?;

        let fn_ty_id =
            Ty::expect_is(original_term_id, Ty::from(fn_def.ty, fn_def_id.origin().inferred()));
        self.infer_ops().check_by_unify(fn_ty_id, annotation_ty)?;

        self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);

        did_check(())
    }

    fn normalise(
        &self,
        _ctx: &mut Context,
        _item: &mut (FnDefId, FnInferMode),
        _item_node: Self::Node,
    ) -> NormaliseResult<()> {
        already_normalised()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        src: &mut (FnDefId, FnInferMode),
        target: &mut (FnDefId, FnInferMode),
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> UnifyResult {
        let (src_id, _) = *src;
        let (target_id, _) = *target;
        if src_id == target_id {
            return Ok(());
        }

        UnifyResult::Err(UnifySignal::CannotUnifyTerms { src: src_node, target: target_node })
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut (FnDefId, FnInferMode)) {
        todo!()
    }
}
