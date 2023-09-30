use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    tir::{Term, TermId, Ty, TyId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    inference::FnInferMode,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        Operations, OperationsOnNode,
    },
};

impl<E: TcEnv> OperationsOnNode<TermId> for Tc<'_, E> {
    type TyNode = TyId;

    fn check_node(&self, term_id: TermId, annotation_ty: Self::TyNode) -> TcResult<()> {
        self.register_new_atom(term_id, annotation_ty);
        match *term_id.value() {
            Term::Tuple(mut tuple_term) => self.check(&mut tuple_term, annotation_ty, term_id)?,
            Term::Lit(lit_term) => self.check_node(lit_term, annotation_ty)?,
            Term::Array(mut prim_term) => { self.check(&mut prim_term, annotation_ty, term_id) }?,
            Term::Ctor(mut ctor_term) => self.check(&mut ctor_term, annotation_ty, term_id)?,
            Term::Call(mut call_term) => self.check(&mut call_term, annotation_ty, term_id)?,
            Term::Fn(mut fn_def_id) => self
                .fn_infer_mode
                .enter(FnInferMode::Body, || self.check(&mut fn_def_id, annotation_ty, term_id))?,
            Term::Var(mut var_term) => self.check(&mut var_term, annotation_ty, term_id)?,
            Term::Return(mut return_term) => {
                self.check(&mut return_term, annotation_ty, term_id)?
            }
            Term::Deref(mut deref_term) => self.check(&mut deref_term, annotation_ty, term_id)?,
            Term::LoopControl(mut loop_control_term) => {
                self.check(&mut loop_control_term, annotation_ty, term_id)?
            }
            Term::Unsafe(mut unsafe_term) => {
                self.check(&mut unsafe_term, annotation_ty, term_id)?
            }
            Term::Loop(mut loop_term) => self.check(&mut loop_term, annotation_ty, term_id)?,
            Term::Block(mut block_term) => self.check(&mut block_term, annotation_ty, term_id)?,
            Term::TyOf(mut ty_of_term) => self.check(&mut ty_of_term, annotation_ty, term_id)?,
            Term::Ref(mut ref_term) => self.check(&mut ref_term, annotation_ty, term_id)?,
            Term::Cast(mut cast_term) => self.check(&mut cast_term, annotation_ty, term_id)?,
            Term::Access(mut access_term) => {
                self.check(&mut access_term, annotation_ty, term_id)?
            }
            Term::Index(mut index_term) => self.check(&mut index_term, annotation_ty, term_id)?,
            Term::Match(mut match_term) => self.check(&mut match_term, annotation_ty, term_id)?,
            Term::Assign(mut assign_term) => {
                self.check(&mut assign_term, annotation_ty, term_id)?
            }
            Term::Intrinsic(mut intrinsic) => self.check(&mut intrinsic, annotation_ty, term_id)?,
            Term::Hole(mut hole) => self.check(&mut hole, annotation_ty, term_id)?,
            Ty::TupleTy(mut tuple_ty) => self.check(&mut tuple_ty, annotation_ty, term_id)?,
            Ty::FnTy(mut fn_ty) => self.check(&mut fn_ty, annotation_ty, term_id)?,
            Ty::RefTy(mut ref_ty) => {
                self.check(&mut ref_ty, annotation_ty, term_id)?;
            }
            Ty::DataTy(mut data_ty) => {
                self.check(&mut data_ty, annotation_ty, term_id)?;
            }
            Ty::Universe(mut universe_ty) => {
                self.check(&mut universe_ty, annotation_ty, term_id)?
            }
        };

        self.check_ty(annotation_ty)?;
        self.register_atom_inference(term_id, term_id, annotation_ty);

        // Potentially evaluate the term.
        self.potentially_run_expr(term_id, annotation_ty)?;
        self.potentially_dump_tir(term_id);

        Ok(())
    }

    fn normalise_node(
        &self,

        _opts: &NormalisationOptions,
        _item: TermId,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify_nodes(
        &self,

        _opts: &UnificationOptions,
        _src: TermId,
        _target: TermId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: TermId) {
        todo!()
    }
}
