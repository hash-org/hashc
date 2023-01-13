// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    args::{ArgsId, PatArgsId},
    defs::{DefArgsId, DefParamsId, DefPatArgsId},
    environment::env::AccessToEnv,
    lits::PrimTerm,
    params::ParamsId,
    terms::{RuntimeTerm, Term, TermId},
    tuples::{TupleTerm, TupleTy},
    tys::TyId,
    utils::common::CommonUtils,
};
use hash_utils::store::CloneStore;

use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcResult, environment::tc_env::TcEnv},
};

#[derive(Constructor)]
pub struct InferOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(InferOps<'tc>);

impl<'tc> InferOps<'tc> {
    pub fn infer_def_params_of_def_pat_args(
        &self,
        _def_pat_args: DefPatArgsId,
    ) -> TcResult<DefParamsId> {
        todo!()
    }

    pub fn infer_def_params_of_def_args(&self, _def_args: DefArgsId) -> TcResult<DefParamsId> {
        todo!()
    }

    pub fn infer_params_of_pat_args(&self, _pat_args: PatArgsId) -> TcResult<ParamsId> {
        todo!()
    }

    pub fn infer_params_of_args(&self, _args: ArgsId) -> TcResult<ParamsId> {
        todo!()
    }

    /// Infer the type of a term, or create a new a type hole.
    pub fn infer_ty_of_term_or_hole(&self, term: TermId) -> TcResult<TyId> {
        Ok(self.infer_ty_of_term(term)?.unwrap_or_else(|| self.new_ty_hole()))
    }

    /// Infer the type of a runtime term.
    pub fn infer_ty_of_runtime_term(&self, term: &RuntimeTerm) -> TyId {
        term.term_ty
    }

    /// Infer the type of a tuple term.
    pub fn infer_ty_of_tuple_term(&self, term: &TupleTerm) -> TcResult<TupleTy> {
        match term.original_ty {
            Some(ty) => Ok(ty),
            None => Ok(TupleTy { data: self.infer_params_of_args(term.data)? }),
        }
    }

    /// Infer the type of a primitive term.
    pub fn infer_ty_of_prim_term(&self, term: &PrimTerm) -> TcResult<TyId> {
        match term {
            PrimTerm::Lit(_) => todo!(),
            PrimTerm::List(_list_term) => todo!(),
        }
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_ty_of_terms(&self, _terms: &[TermId]) -> TcResult<TyId> {
        todo!()
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_ty_of_term(&self, term_id: TermId) -> TcResult<Option<TyId>> {
        self.stores().term().map(term_id, |term| {
            match term {
                Term::Runtime(rt_term) => Ok(Some(self.infer_ty_of_runtime_term(rt_term))),
                Term::Tuple(tuple_term) => {
                    Ok(Some(self.new_ty(self.infer_ty_of_tuple_term(tuple_term)?)))
                }
                Term::Prim(_) => todo!(),
                Term::Ctor(_) => {
                    todo!()
                }
                Term::FnCall(_) => todo!(),
                Term::FnRef(_fn_def_id) => todo!(),
                Term::Block(_) => todo!(),
                Term::Var(_) => todo!(),
                Term::Loop(_) => {
                    // @@Future: if loop is proven to not break, return never
                    todo!()
                }
                Term::LoopControl(_) => todo!(),
                Term::Match(_) => todo!(),
                Term::Return(_) => todo!(),
                Term::DeclStackMember(_) => todo!(),
                Term::Assign(_) => todo!(),
                Term::Unsafe(_) => todo!(),
                Term::Access(_) => todo!(),
                Term::Cast(_) => todo!(),
                Term::TypeOf(_) => todo!(),
                Term::Ty(_ty_id) => {
                    todo!()
                    // match self.get_ty(ty_id) {
                    //     Ty::Hole(_) =>
                    // Err(TcError::NeedMoreTypeAnnotationsToInfer { term }),
                    //     Ty::Tuple(_) | Ty::Fn(_) | Ty::Ref(_) | Ty::Data(_)
                    // => {         // @@Todo: bounds
                    //         Ok(self.new_small_universe_ty())
                    //     }
                    //     Ty::Universe(universe_ty) =>
                    // Ok(self.new_universe_ty(universe_ty.size + 1)),
                    //     Ty::Var(_) => todo!(),
                    //     Ty::Eval(_) => todo!(),
                    // }
                }
                Term::Ref(_ref_term) => {
                    todo!()
                    // let inner_ty =
                    // self.infer_ty_of_term_or_hole(ref_term.subject);
                    // Ok(Some(self.new_ty(Ty::Ref(RefTy {
                    //     ty: inner_ty,
                    //     mutable: ref_term.mutable,
                    //     kind: ref_term.kind,
                    // }))))
                }
                Term::Deref(_) => todo!(),
                Term::Hole(_) => {
                    todo!()
                }
            }
        })
    }
}
