use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    tir::{
        node::NodeOrigin,
        terms::{Term, TermId, Ty, TyId},
    },
};

use crate::{
    checker::Checker,
    env::TcEnv,
    inference::FnInferMode,
    operations::{
        checking::{checked, CheckResult},
        normalisation::NormaliseResult,
        Operations,
    },
};

impl<E: TcEnv> Operations<TermId> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _: &mut hash_tir::context::Context,
        term_id: &mut TermId,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> CheckResult {
        let term_id = *term_id;
        self.register_new_atom(term_id, annotation_ty);
        let inference = self.infer_ops();
        let expects_ty =
            |ty: TyId| inference.check_by_unify(ty, Ty::universe(NodeOrigin::Expected));

        match *term_id.value() {
            Term::Tuple(tuple_term) => {
                inference.infer_tuple_term(&tuple_term, annotation_ty, term_id)?
            }
            Term::Lit(lit_term) => inference.infer_lit(lit_term, annotation_ty)?,
            Term::Array(prim_term) => inference.infer_array_term(&prim_term, annotation_ty)?,
            Term::Ctor(ctor_term) => {
                inference.infer_ctor_term(&ctor_term, annotation_ty, term_id)?
            }
            Term::Call(fn_call_term) => {
                inference.infer_fn_call_term(&fn_call_term, annotation_ty, term_id)?
            }
            Term::Fn(fn_def_id) => {
                inference.infer_fn_def(fn_def_id, annotation_ty, term_id, FnInferMode::Body)?
            }
            Term::Var(var_term) => inference.infer_var(var_term, annotation_ty)?,
            Term::Return(return_term) => {
                inference.infer_return_term(&return_term, annotation_ty, term_id)?
            }
            Term::Deref(deref_term) => inference.infer_deref_term(&deref_term, annotation_ty)?,
            Term::LoopControl(loop_control_term) => {
                inference.infer_loop_control_term(&loop_control_term, annotation_ty)?
            }
            Term::Unsafe(unsafe_term) => {
                inference.infer_unsafe_term(&unsafe_term, annotation_ty)?
            }
            Term::Loop(loop_term) => {
                inference.infer_loop_term(&loop_term, annotation_ty, term_id)?
            }
            Term::Block(block_term) => {
                inference.infer_block_term(&block_term, annotation_ty, term_id)?
            }
            Term::TypeOf(ty_of_term) => {
                inference.infer_ty_of_term(ty_of_term, annotation_ty, term_id)?
            }
            Term::Ref(ref_term) => inference.infer_ref_term(&ref_term, annotation_ty, term_id)?,
            Term::Cast(cast_term) => inference.infer_cast_term(cast_term, annotation_ty)?,
            Term::Access(access_term) => {
                inference.infer_access_term(&access_term, annotation_ty, term_id)?
            }
            Term::Index(index_term) => {
                inference.infer_index_term(&index_term, annotation_ty, term_id)?
            }
            Term::Match(match_term) => inference.infer_match_term(&match_term, annotation_ty)?,
            Term::Assign(assign_term) => {
                inference.infer_assign_term(&assign_term, annotation_ty, term_id)?
            }
            Term::Intrinsic(intrinsic) => inference.infer_intrinsic(intrinsic, annotation_ty)?,
            Term::Hole(_) => {}
            Ty::TupleTy(tuple_ty) => {
                inference.infer_params(tuple_ty.data, || Ok(()))?;
                expects_ty(annotation_ty)?;
            }
            Ty::FnTy(fn_ty) => {
                inference.infer_params(fn_ty.params, || {
                    inference.infer_term(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
                })?;
                expects_ty(annotation_ty)?;
            }
            Ty::RefTy(ref_ty) => {
                // Infer the inner type
                inference.infer_term(ref_ty.ty, Ty::universe(NodeOrigin::Expected))?;
                expects_ty(annotation_ty)?;
            }
            Ty::DataTy(mut data_ty) => {
                let data_def = data_ty.data_def.value();
                let copied_params = inference.sub_ops().copy_params(data_def.params);
                inference.infer_args(data_ty.args, copied_params, |inferred_data_ty_args| {
                    data_ty.args = inferred_data_ty_args;
                    term_id.set(term_id.value().with_data(data_ty.into()));
                    Ok(())
                })?;
                expects_ty(annotation_ty)?;
            }
            Ty::Universe => {
                expects_ty(annotation_ty)?;
            }
        };

        inference.check_ty(annotation_ty)?;
        self.register_atom_inference(term_id, term_id, annotation_ty);

        // Potentially evaluate the term.
        inference.potentially_run_expr(term_id, annotation_ty)?;
        inference.potentially_dump_tir(term_id);

        checked()
    }

    fn normalise(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _item: &mut TermId,
        _: Self::Node,
    ) -> NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _src: &mut TermId,
        _target: &mut TermId,
        _: Self::Node,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: &mut TermId,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }
}
