use derive_more::{Constructor, From};

use super::common::CommonUtils;
use crate::{
    impl_access_to_env,
    new::{
        args::{ArgsId, PatArgsId},
        defs::{DefArgsId, DefParamsId, DefPatArgsId},
        environment::env::Env,
        lits::PrimTerm,
        params::ParamsId,
        pats::{Pat, PatId},
        terms::{Term, TermId},
        tys::{Ty, TyId},
    },
};

#[derive(Constructor)]
pub struct TraversingUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(TraversingUtils<'env>);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, From)]
pub enum TermOrPatOrTy {
    Term(TermId),
    Ty(TyId),
    Pat(PatId),
}

struct TraverseImplState<F> {
    depth: usize,
    f: F,
}

impl<'env> TraversingUtils<'env> {
    pub fn traverse_term<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        term_id: TermId,
        f: F,
    ) -> Result<(), E> {
        self.traverse_term_impl(term_id, &mut TraverseImplState { depth: 0, f })
    }

    pub fn traverse_ty<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        ty_id: TyId,
        f: F,
    ) -> Result<(), E> {
        self.traverse_ty_impl(ty_id, &mut TraverseImplState { depth: 0, f })
    }

    pub fn traverse_pat<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        pat_id: PatId,
        f: F,
    ) -> Result<(), E> {
        self.traverse_pat_impl(pat_id, &mut TraverseImplState { depth: 0, f })
    }

    pub fn traverse_term_or_pat_or_ty<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        term_or_ty: TermOrPatOrTy,
        f: F,
    ) -> Result<(), E> {
        match term_or_ty {
            TermOrPatOrTy::Term(term_id) => self.traverse_term(term_id, f),
            TermOrPatOrTy::Ty(ty_id) => self.traverse_ty(ty_id, f),
            TermOrPatOrTy::Pat(pat_id) => self.traverse_pat(pat_id, f),
        }
    }

    fn traverse_params_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        params: ParamsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_params(params, |params| {
            for param in params.iter() {
                self.child(state, |state| self.traverse_ty_impl(param.ty, state))?;
            }
            Ok(())
        })
    }

    fn child<F, T>(
        &self,
        state: &mut TraverseImplState<F>,
        f: impl FnOnce(&mut TraverseImplState<F>) -> T,
    ) -> T {
        state.depth += 1;
        let result = f(state);
        state.depth -= 1;
        result
    }

    fn traverse_args_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        args: ArgsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_args(args, |args| {
            for arg in args.iter() {
                self.child(state, |state| self.traverse_term_impl(arg.value, state))?;
            }
            Ok(())
        })
    }

    fn traverse_pat_args_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        pat_args: PatArgsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_pat_args(pat_args, |pat_args| {
            for pat_arg in pat_args.iter() {
                self.child(state, |state| self.traverse_pat_impl(pat_arg.pat, state))?;
            }
            Ok(())
        })
    }

    fn traverse_def_params_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        def_params: DefParamsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_def_params(def_params, |def_params| {
            for def_param in def_params.iter() {
                self.traverse_params_impl(def_param.params, state)?;
            }
            Ok(())
        })
    }

    fn traverse_def_args_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        def_args: DefArgsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_def_args(def_args, |def_args| {
            for def_arg in def_args.iter() {
                self.traverse_args_impl(def_arg.args, state)?;
            }
            Ok(())
        })
    }

    fn traverse_def_pat_args_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        def_pat_args: DefPatArgsId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_def_pat_args(def_pat_args, |def_pat_args| {
            for def_arg in def_pat_args.iter() {
                self.traverse_pat_args_impl(def_arg.pat_args, state)?;
            }
            Ok(())
        })
    }

    fn traverse_ty_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        ty_id: TyId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_ty(ty_id, |ty| match ty {
            Ty::Tuple(tuple_tu) => self.traverse_params_impl(tuple_tu.data, state),
            Ty::Fn(_fn_ty) => todo!(),
            Ty::Ref(_) => todo!(),
            Ty::Hole(_) => todo!(),
            Ty::Eval(_) => todo!(),
            Ty::Var(_) => todo!(),
            Ty::Data(_) => todo!(),
            Ty::Universe(_) => todo!(),
        })
    }

    fn traverse_pat_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        pat_id: PatId,
        _state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_pat(pat_id, |pat| match pat {
            Pat::Binding(_) => todo!(),
            Pat::Range(_) => todo!(),
            Pat::Lit(_) => todo!(),
            Pat::Tuple(_) => todo!(),
            Pat::List(_) => todo!(),
            Pat::Ctor(_) => todo!(),
            Pat::Or(_) => todo!(),
            Pat::If(_) => todo!(),
        })
    }

    fn traverse_term_impl<F: FnMut(TermOrPatOrTy) -> Result<(), E>, E>(
        &self,
        term_id: TermId,
        state: &mut TraverseImplState<F>,
    ) -> Result<(), E> {
        self.map_term(term_id, |term| match term {
            Term::Runtime(rt) => self.traverse_ty_impl(rt.term_ty, state),
            Term::Tuple(tu) => self.traverse_args_impl(tu.data, state),
            Term::Prim(prim_term) => match prim_term {
                PrimTerm::Lit(_) => Ok(()),
                PrimTerm::List(list) => self.map_term_list(list.elements, |items| {
                    for &item in items {
                        self.traverse_term_impl(item, state)?;
                    }
                    Ok(())
                }),
            },
            Term::Ctor(ctor_term) => {
                self.traverse_def_args_impl(ctor_term.data_args, state)?;
                self.traverse_def_args_impl(ctor_term.ctor_args, state)?;
                Ok(())
            }
            Term::FnCall(fn_call_term) => {
                self.traverse_term_impl(fn_call_term.subject, state)?;
                self.traverse_args_impl(fn_call_term.args, state)?;
                Ok(())
            }
            Term::FnRef(_) => todo!(),
            Term::Block(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Loop(_) => todo!(),
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => todo!(),
            Term::DeclStackMember(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(_) => todo!(),
            Term::Ref(_) => todo!(),
            Term::Deref(_) => todo!(),
            Term::Hole(_) => todo!(),
            Term::HoleBinder(_) => todo!(),
        })
    }
}
