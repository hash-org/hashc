use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::ScopeKind,
    tir::{FnDefId, FnTy, NodeId, NodeOrigin, Term, TermId, Ty, TyId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    inference::FnInferMode,
    operations::{
        normalisation::{already_normalised, NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations, OperationsOnNode,
    },
};

impl<E: TcEnv> Operations<FnTy> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(&self, fn_ty: &mut FnTy, item_ty: Self::TyNode, _: Self::Node) -> TcResult<()> {
        self.check_is_universe(item_ty)?;
        self.infer_params(fn_ty.params, || {
            self.check_node(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
        })?;
        Ok(())
    }

    fn normalise(
        &self,

        _opts: &NormalisationOptions,
        _item: FnTy,
        _item_node: Self::Node,
    ) -> NormaliseResult<TyId> {
        already_normalised()
    }

    fn unify(
        &self,

        _opts: &UnificationOptions,
        f1: &mut FnTy,
        f2: &mut FnTy,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> TcResult<()> {
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

impl<E: TcEnv> Operations<FnDefId> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        fn_def_id: &mut FnDefId,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let fn_def_id = *fn_def_id;
        self.check_ty(annotation_ty)?;
        if let Some(fn_ty) = self.try_get_inferred_ty(fn_def_id) {
            let expected =
                Ty::expect_is(original_term_id, Ty::from(fn_ty, fn_def_id.origin().inferred()));
            self.check_by_unify(expected, annotation_ty)?;
            return Ok(());
        }

        self.infer_fn_annotation_ty(fn_def_id, annotation_ty)?;
        let fn_def = fn_def_id.value();

        if self.fn_infer_mode.get() == FnInferMode::Header {
            // If we are only inferring the header, then we also want to check for
            // immediate body functions.
            self.infer_params(fn_def.ty.params, || {
                self.check_node(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                if let Term::Fn(mut immediate_body_fn) = *fn_def.body.value() {
                    self.check(&mut immediate_body_fn, Ty::hole_for(fn_def.body), fn_def.body)?;
                }
                Ok(())
            })?;
            return Ok(());
        }

        if self.atom_is_registered(fn_def_id) {
            // Recursive call
            return Ok(());
        }

        self.register_new_atom(fn_def_id, fn_def.ty);

        let fn_def = fn_def_id.value();

        self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
            self.infer_params(fn_def.ty.params, || {
                self.check_node(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                self.check_node(fn_def.body, fn_def.ty.return_ty)
            })
        })?;

        let fn_ty_id =
            Ty::expect_is(original_term_id, Ty::from(fn_def.ty, fn_def_id.origin().inferred()));
        self.check_by_unify(fn_ty_id, annotation_ty)?;

        self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);

        Ok(())
    }

    fn normalise(
        &self,

        _opts: &NormalisationOptions,
        _item: FnDefId,
        _item_node: Self::Node,
    ) -> NormaliseResult<TermId> {
        already_normalised()
    }

    fn unify(
        &self,

        opts: &UnificationOptions,
        src: &mut FnDefId,
        target: &mut FnDefId,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        let src_id = *src;
        let target_id = *target;
        if src_id == target_id {
            return Ok(());
        }

        self.uni_ops_with(opts).mismatching_atoms(src_node, target_node)
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut FnDefId) {
        todo!()
    }
}
