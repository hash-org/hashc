use std::ops::ControlFlow;

///! Utilities to traverse the term structure.
use derive_more::{Constructor, From, TryInto};

use super::{common::CommonUtils, AccessToUtils};
use crate::{
    impl_access_to_env,
    new::{
        access::AccessTerm,
        args::{ArgData, ArgsId, PatArgData, PatArgsId},
        casting::CastTerm,
        control::{IfPat, LoopTerm, MatchTerm, OrPat, ReturnTerm},
        data::{CtorPat, CtorTerm, DataTy},
        defs::{
            DefArgGroupData, DefArgsId, DefParamGroupData, DefParamsId, DefPatArgGroupData,
            DefPatArgsId,
        },
        environment::env::Env,
        fns::{FnBody, FnCallTerm, FnDefData, FnDefId, FnTy},
        holes::{HoleBinder, HoleBinderKind},
        lits::{ListCtor, ListPat, PrimTerm},
        params::{ParamData, ParamsId},
        pats::{Pat, PatId, PatListId},
        refs::{DerefTerm, RefTerm, RefTy},
        scopes::{AssignTerm, BlockTerm, DeclStackMemberTerm},
        terms::{RuntimeTerm, Term, TermId, TermListId, UnsafeTerm},
        tuples::{TuplePat, TupleTerm, TupleTy},
        tys::{Ty, TyId, TypeOfTerm},
    },
};

// @@Temp
#[allow(unused)]
#[derive(Constructor)]
pub struct TraversingUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(TraversingUtils<'env>);

/// A term, type or pattern.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, From, TryInto)]
pub enum Atom {
    Term(TermId),
    Ty(TyId),
    FnDef(FnDefId),
    Pat(PatId),
}

struct _TraverseImplState<'b, B, F> {
    depth: usize,
    accumulator: &'b mut B,
    f: F,
}

pub trait Folder<B, E> = Fn(&mut B, Atom) -> Result<ControlFlow<()>, E> + Copy;

pub trait FMapper<E> = Fn(Atom) -> Result<ControlFlow<Atom>, E> + Copy;

impl<'env> TraversingUtils<'env> {
    pub fn fmap_atom<E, F: FMapper<E>>(&self, atom: Atom, f: F) -> Result<Atom, E> {
        match f(atom)? {
            ControlFlow::Break(atom) => Ok(atom),
            ControlFlow::Continue(()) => match atom {
                Atom::Term(term_id) => Ok(Atom::Term(self.fmap_term(term_id, f)?)),
                Atom::Ty(ty_id) => Ok(Atom::Ty(self.fmap_ty(ty_id, f)?)),
                Atom::FnDef(fn_def_id) => Ok(Atom::FnDef(self.fmap_fn_def(fn_def_id, f)?)),
                Atom::Pat(pat_id) => Ok(Atom::Pat(self.fmap_pat(pat_id, f)?)),
            },
        }
    }

    pub fn fmap_term<E, F: FMapper<E>>(&self, term_id: TermId, f: F) -> Result<TermId, E> {
        match f(term_id.into())? {
            ControlFlow::Break(atom) => Ok(TermId::try_from(atom).unwrap()),
            ControlFlow::Continue(()) => match self.get_term(term_id) {
                Term::Runtime(rt_term) => {
                    let term_ty = self.fmap_ty(rt_term.term_ty, f)?;
                    Ok(self.new_term(RuntimeTerm { term_ty }))
                }
                Term::Tuple(tuple_term) => {
                    let data = self.fmap_args(tuple_term.data, f)?;
                    Ok(self.new_term(Term::Tuple(TupleTerm { data })))
                }
                Term::Prim(prim_term) => match prim_term {
                    PrimTerm::Lit(lit) => Ok(self.new_term(Term::Prim(PrimTerm::Lit(lit)))),
                    PrimTerm::List(list_ctor) => {
                        let elements = self.fmap_term_list(list_ctor.elements, f)?;
                        Ok(self.new_term(Term::Prim(PrimTerm::List(ListCtor { elements }))))
                    }
                },
                Term::Ctor(ctor_term) => {
                    let data_args = self.fmap_def_args(ctor_term.data_args, f)?;
                    let ctor_args = self.fmap_def_args(ctor_term.ctor_args, f)?;
                    Ok(self.new_term(CtorTerm { ctor: ctor_term.ctor, data_args, ctor_args }))
                }
                Term::FnCall(fn_call_term) => {
                    let subject = self.fmap_term(fn_call_term.subject, f)?;
                    let args = self.fmap_args(fn_call_term.args, f)?;
                    Ok(self.new_term(FnCallTerm { args, subject, implicit: fn_call_term.implicit }))
                }
                Term::FnRef(fn_def_id) => {
                    let fn_def_id = self.fmap_fn_def(fn_def_id, f)?;
                    Ok(self.new_term(Term::FnRef(fn_def_id)))
                }
                Term::Block(block_term) => {
                    let statements = self.fmap_term_list(block_term.statements, f)?;
                    let return_value = self.fmap_term(block_term.return_value, f)?;
                    Ok(self.new_term(BlockTerm { statements, return_value }))
                }
                Term::Var(var_term) => Ok(self.new_term(var_term)),
                Term::Loop(loop_term) => {
                    let statements = self.fmap_term_list(loop_term.block.statements, f)?;
                    let return_value = self.fmap_term(loop_term.block.return_value, f)?;
                    Ok(self.new_term(LoopTerm { block: BlockTerm { statements, return_value } }))
                }
                Term::LoopControl(loop_control_term) => Ok(self.new_term(loop_control_term)),
                Term::Match(match_term) => {
                    let subject = self.fmap_term(match_term.subject, f)?;
                    let cases = self.fmap_pat_list(match_term.cases, f)?;
                    let decisions = self.fmap_term_list(match_term.decisions, f)?;
                    Ok(self.new_term(MatchTerm { cases, decisions, subject }))
                }
                Term::Return(return_term) => {
                    let expression = self.fmap_term(return_term.expression, f)?;
                    Ok(self.new_term(ReturnTerm { expression }))
                }
                Term::DeclStackMember(decl_stack_member_term) => {
                    let bind_pat = self.fmap_pat(decl_stack_member_term.bind_pat, f)?;
                    let ty = self.fmap_ty(decl_stack_member_term.ty, f)?;
                    let value =
                        decl_stack_member_term.value.map(|v| self.fmap_term(v, f)).transpose()?;
                    Ok(self.new_term(DeclStackMemberTerm { ty, bind_pat, value }))
                }
                Term::Assign(assign_term) => {
                    let subject = self.fmap_term(assign_term.subject, f)?;
                    let value = self.fmap_term(assign_term.value, f)?;
                    Ok(self.new_term(AssignTerm { subject, value }))
                }
                Term::Unsafe(unsafe_term) => {
                    let inner = self.fmap_term(unsafe_term.inner, f)?;
                    Ok(self.new_term(UnsafeTerm { inner }))
                }
                Term::Access(access_term) => {
                    let subject = self.fmap_term(access_term.subject, f)?;
                    Ok(self.new_term(AccessTerm { subject, field: access_term.field }))
                }
                Term::Cast(cast_term) => {
                    let subject_term = self.fmap_term(cast_term.subject_term, f)?;
                    let target_ty = self.fmap_ty(cast_term.target_ty, f)?;
                    Ok(self.new_term(CastTerm { subject_term, target_ty }))
                }
                Term::TypeOf(type_of_term) => {
                    let term = self.fmap_term(type_of_term.term, f)?;
                    Ok(self.new_term(TypeOfTerm { term }))
                }
                Term::Ty(ty) => {
                    let ty = self.fmap_ty(ty, f)?;
                    Ok(self.new_term(ty))
                }
                Term::Ref(ref_term) => {
                    let subject = self.fmap_term(ref_term.subject, f)?;
                    Ok(self.new_term(RefTerm {
                        subject,
                        kind: ref_term.kind,
                        mutable: ref_term.mutable,
                    }))
                }
                Term::Deref(deref_term) => {
                    let subject = self.fmap_term(deref_term.subject, f)?;
                    Ok(self.new_term(DerefTerm { subject }))
                }
                Term::Hole(hole_term) => Ok(self.new_term(hole_term)),
                Term::HoleBinder(hole_binder) => match hole_binder.kind {
                    HoleBinderKind::Hole(ty) => {
                        let ty = self.fmap_ty(ty, f)?;
                        let inner = self.fmap_term(hole_binder.inner, f)?;
                        Ok(self.new_term(HoleBinder {
                            hole: hole_binder.hole,
                            inner,
                            kind: HoleBinderKind::Hole(ty),
                        }))
                    }
                    HoleBinderKind::Guess(guess) => {
                        let guess = self.fmap_term(guess, f)?;
                        let inner = self.fmap_term(hole_binder.inner, f)?;
                        Ok(self.new_term(HoleBinder {
                            hole: hole_binder.hole,
                            inner,
                            kind: HoleBinderKind::Guess(guess),
                        }))
                    }
                },
            },
        }
    }

    pub fn fmap_ty<E, F: FMapper<E>>(&self, ty_id: TyId, f: F) -> Result<TyId, E> {
        match f(ty_id.into())? {
            ControlFlow::Break(ty) => Ok(TyId::try_from(ty).unwrap()),
            ControlFlow::Continue(()) => match self.get_ty(ty_id) {
                Ty::Eval(eval_term) => {
                    let eval_term = self.fmap_term(eval_term, f)?;
                    Ok(self.new_ty(eval_term))
                }
                Ty::Hole(hole_ty) => Ok(self.new_ty(hole_ty)),
                Ty::Var(var_ty) => Ok(self.new_ty(var_ty)),
                Ty::Tuple(tuple_ty) => {
                    let data = self.fmap_params(tuple_ty.data, f)?;
                    Ok(self.new_ty(TupleTy { data }))
                }
                Ty::Fn(fn_ty) => {
                    let params = self.fmap_params(fn_ty.params, f)?;
                    let return_ty = self.fmap_ty(fn_ty.return_ty, f)?;
                    Ok(self.new_ty(FnTy {
                        params,
                        return_ty,
                        implicit: fn_ty.implicit,
                        is_unsafe: fn_ty.is_unsafe,
                        pure: fn_ty.pure,
                    }))
                }
                Ty::Ref(ref_ty) => {
                    let ty = self.fmap_ty(ref_ty.ty, f)?;
                    Ok(self.new_ty(RefTy { ty, kind: ref_ty.kind, mutable: ref_ty.mutable }))
                }
                Ty::Data(data_ty) => {
                    let args = self.fmap_def_args(data_ty.args, f)?;
                    Ok(self.new_ty(DataTy { args, data_def: data_ty.data_def }))
                }
                Ty::Universe(universe_ty) => Ok(self.new_ty(universe_ty)),
            },
        }
    }

    pub fn fmap_pat<E, F: FMapper<E>>(&self, pat_id: PatId, f: F) -> Result<PatId, E> {
        match f(pat_id.into())? {
            ControlFlow::Break(pat) => Ok(PatId::try_from(pat).unwrap()),
            ControlFlow::Continue(()) => match self.get_pat(pat_id) {
                Pat::Binding(binding_pat) => Ok(self.new_pat(binding_pat)),
                Pat::Range(range_pat) => Ok(self.new_pat(range_pat)),
                Pat::Lit(lit_pat) => Ok(self.new_pat(lit_pat)),
                Pat::Tuple(tuple_pat) => {
                    let data = self.fmap_pat_args(tuple_pat.data, f)?;
                    Ok(self.new_pat(TuplePat { data_spread: tuple_pat.data_spread, data }))
                }
                Pat::List(list_pat) => {
                    let pats = self.fmap_pat_list(list_pat.pats, f)?;
                    Ok(self.new_pat(ListPat { spread: list_pat.spread, pats }))
                }
                Pat::Ctor(ctor_pat) => {
                    let data_args = self.fmap_def_args(ctor_pat.data_args, f)?;
                    let ctor_pat_args = self.fmap_def_pat_args(ctor_pat.ctor_pat_args, f)?;
                    Ok(self.new_pat(CtorPat { data_args, ctor_pat_args, ctor: ctor_pat.ctor }))
                }
                Pat::Or(or_pat) => {
                    let alternatives = self.fmap_pat_list(or_pat.alternatives, f)?;
                    Ok(self.new_pat(OrPat { alternatives }))
                }
                Pat::If(if_pat) => {
                    let pat = self.fmap_pat(if_pat.pat, f)?;
                    let condition = self.fmap_term(if_pat.condition, f)?;
                    Ok(self.new_pat(IfPat { pat, condition }))
                }
            },
        }
    }

    pub fn fmap_term_list<E, F: FMapper<E>>(
        &self,
        term_list: TermListId,
        f: F,
    ) -> Result<TermListId, E> {
        self.map_term_list(term_list, |term_list| {
            let mut new_list = Vec::with_capacity(term_list.len());
            for term_id in term_list {
                new_list.push(self.fmap_term(*term_id, f)?);
            }
            Ok(self.new_term_list(new_list))
        })
    }

    pub fn fmap_pat_list<E, F: FMapper<E>>(
        &self,
        pat_list: PatListId,
        f: F,
    ) -> Result<PatListId, E> {
        self.map_pat_list(pat_list, |pat_list| {
            let mut new_list = Vec::with_capacity(pat_list.len());
            for pat_id in pat_list {
                new_list.push(self.fmap_pat(*pat_id, f)?);
            }
            Ok(self.new_pat_list(new_list))
        })
    }

    pub fn fmap_params<E, F: FMapper<E>>(&self, params_id: ParamsId, f: F) -> Result<ParamsId, E> {
        self.map_params(params_id, |params| {
            let mut new_params = Vec::with_capacity(params.len());
            for param in params {
                new_params.push(ParamData { name: param.name, ty: self.fmap_ty(param.ty, f)? });
            }
            Ok(self.param_utils().create_params(new_params.into_iter()))
        })
    }

    pub fn fmap_args<E, F: FMapper<E>>(&self, args_id: ArgsId, f: F) -> Result<ArgsId, E> {
        self.map_args(args_id, |args| {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                new_args.push(ArgData { target: arg.target, value: self.fmap_term(arg.value, f)? });
            }
            Ok(self.param_utils().create_args(new_args.into_iter()))
        })
    }

    pub fn fmap_def_args<E, F: FMapper<E>>(
        &self,
        def_args_id: DefArgsId,
        f: F,
    ) -> Result<DefArgsId, E> {
        self.map_def_args(def_args_id, |def_args| {
            let mut new_args = Vec::with_capacity(def_args.len());
            for def_arg in def_args {
                new_args.push(DefArgGroupData {
                    args: self.fmap_args(def_arg.args, f)?,
                    implicit: def_arg.implicit,
                });
            }
            Ok(self.param_utils().create_def_args(new_args.into_iter()))
        })
    }

    pub fn fmap_def_params<E, F: FMapper<E>>(
        &self,
        def_params_id: DefParamsId,
        f: F,
    ) -> Result<DefParamsId, E> {
        self.map_def_params(def_params_id, |def_params| {
            let mut new_params = Vec::with_capacity(def_params.len());
            for def_param in def_params {
                new_params.push(DefParamGroupData {
                    implicit: def_param.implicit,
                    params: self.fmap_params(def_param.params, f)?,
                });
            }
            Ok(self.param_utils().create_def_params(new_params.into_iter()))
        })
    }

    pub fn fmap_pat_args<E, F: FMapper<E>>(
        &self,
        pat_args_id: PatArgsId,
        f: F,
    ) -> Result<PatArgsId, E> {
        self.map_pat_args(pat_args_id, |pat_args| {
            let mut new_args = Vec::with_capacity(pat_args.len());
            for pat_arg in pat_args {
                new_args.push(PatArgData {
                    target: pat_arg.target,
                    pat: self.fmap_pat(pat_arg.pat, f)?,
                });
            }
            Ok(self.param_utils().create_pat_args(new_args.into_iter()))
        })
    }

    pub fn fmap_def_pat_args<E, F: FMapper<E>>(
        &self,
        def_pat_args_id: DefPatArgsId,
        f: F,
    ) -> Result<DefPatArgsId, E> {
        self.map_def_pat_args(def_pat_args_id, |def_pat_args| {
            let mut new_args = Vec::with_capacity(def_pat_args.len());
            for def_pat_arg in def_pat_args {
                new_args.push(DefPatArgGroupData {
                    pat_args: self.fmap_pat_args(def_pat_arg.pat_args, f)?,
                    spread: def_pat_arg.spread,
                    implicit: def_pat_arg.implicit,
                });
            }
            Ok(self.param_utils().create_def_pat_args(new_args.into_iter()))
        })
    }

    pub fn fmap_fn_def<E, F: FMapper<E>>(&self, fn_def_id: FnDefId, f: F) -> Result<FnDefId, E> {
        match f(fn_def_id.into())? {
            ControlFlow::Break(fn_def_id) => Ok(FnDefId::try_from(fn_def_id).unwrap()),
            ControlFlow::Continue(()) => {
                let fn_def = self.get_fn_def(fn_def_id);
                Ok(self.fn_utils().create_fn_def(FnDefData {
                    name: fn_def.name,
                    ty: {
                        let fn_ty = fn_def.ty;
                        FnTy {
                            params: self.fmap_params(fn_ty.params, f)?,
                            return_ty: self.fmap_ty(fn_ty.return_ty, f)?,
                            implicit: fn_ty.implicit,
                            is_unsafe: fn_ty.is_unsafe,
                            pure: fn_ty.pure,
                        }
                    },
                    body: match fn_def.body {
                        FnBody::Defined(defined) => FnBody::Defined(self.fmap_term(defined, f)?),
                        FnBody::Intrinsic(_) | FnBody::Axiom => fn_def.body, // no-op
                    },
                }))
            }
        }
    }

    // pub fn fold_term<B, E, F: Folder<B, E>>(
    //     &self,
    //     term_id: TermId,
    //     mut initial: B,
    //     f: F,
    // ) -> Result<B, E> {
    //     let mut state = TraverseImplState { depth: 0, f, accumulator: &mut
    // initial };     self.traverse_term_children_impl(term_id, &mut state)?;
    //     Ok(initial)
    // }

    // pub fn fold_ty<B, E, F: Folder<B, E>>(
    //     &self,
    //     ty_id: TyId,
    //     mut initial: B,
    //     f: F,
    // ) -> Result<B, E> {
    //     let mut state = TraverseImplState { depth: 0, f, accumulator: &mut
    // initial };     self.traverse_ty_children_impl(ty_id, &mut state)?;
    //     Ok(initial)
    // }

    // pub fn fold_pat<B, E, F: Folder<B, E>>(
    //     &self,
    //     pat_id: PatId,
    //     mut initial: B,
    //     f: F,
    // ) -> Result<B, E> {
    //     let mut state = TraverseImplState { depth: 0, f, accumulator: &mut
    // initial };     self.traverse_pat_children_impl(pat_id, &mut state)?;
    //     Ok(initial)
    // }

    // pub fn fold_atom<B, E, F: Folder<B, E>>(
    //     &self,
    //     term_or_ty: Atom,
    //     initial: B,
    //     f: F,
    // ) -> Result<B, E> {
    //     match term_or_ty {
    //         Atom::Term(term_id) => self.fold_term(term_id, initial, f),
    //         Atom::Ty(ty_id) => self.fold_ty(ty_id, initial, f),
    //         Atom::Pat(pat_id) => self.fold_pat(pat_id, initial, f),
    //         Atom::FnDef(_) => todo!(),
    //     }
    // }

    // fn traverse_params_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     params: ParamsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_params(params, |params| {
    //         for param in params.iter() {
    //             self.child(state, |state|
    // self.traverse_ty_children_impl(param.ty, state))?;         }
    //         Ok(())
    //     })
    // }

    // fn child<B, F, T>(
    //     &self,
    //     state: &mut TraverseImplState<B, F>,
    //     f: impl FnOnce(&mut TraverseImplState<B, F>) -> T,
    // ) -> T {
    //     state.depth += 1;
    //     let result = f(state);
    //     state.depth -= 1;
    //     result
    // }

    // fn traverse_args_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     args: ArgsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_args(args, |args| {
    //         for arg in args.iter() {
    //             self.child(state, |state|
    // self.traverse_term_children_impl(arg.value, state))?;         }
    //         Ok(())
    //     })
    // }

    // fn _traverse_pat_args_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     pat_args: PatArgsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_pat_args(pat_args, |pat_args| {
    //         for pat_arg in pat_args.iter() {
    //             self.child(state, |state|
    // self.traverse_pat_children_impl(pat_arg.pat, state))?;         }
    //         Ok(())
    //     })
    // }

    // fn _traverse_def_params_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     def_params: DefParamsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_def_params(def_params, |def_params| {
    //         for def_param in def_params.iter() {
    //             self.traverse_params_impl(def_param.params, state)?;
    //         }
    //         Ok(())
    //     })
    // }

    // fn traverse_def_args_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     def_args: DefArgsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_def_args(def_args, |def_args| {
    //         for def_arg in def_args.iter() {
    //             self.traverse_args_impl(def_arg.args, state)?;
    //         }
    //         Ok(())
    //     })
    // }

    // fn _traverse_def_pat_args_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     def_pat_args: DefPatArgsId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.map_def_pat_args(def_pat_args, |def_pat_args| {
    //         for def_arg in def_pat_args.iter() {
    //             self._traverse_pat_args_impl(def_arg.pat_args, state)?;
    //         }
    //         Ok(())
    //     })
    // }

    // fn traverse_ty_children_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     ty_id: TyId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.fmap_ty(ty_id, |ty| match ty {
    //         Ty::Tuple(tuple_tu) => todo!(),
    //         Ty::Fn(_fn_ty) => todo!(),
    //         Ty::Ref(_) => todo!(),
    //         Ty::Hole(_) => todo!(),
    //         Ty::Eval(_) => todo!(),
    //         Ty::Var(_) => todo!(),
    //         Ty::Data(_) => todo!(),
    //         Ty::Universe(_) => todo!(),
    //     })
    // }

    // fn traverse_pat_children_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     pat_id: PatId,
    //     _state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.fmap_pat(pat_id, |pat| match pat {
    //         Pat::Binding(_) => todo!(),
    //         Pat::Range(_) => todo!(),
    //         Pat::Lit(_) => todo!(),
    //         Pat::Tuple(_) => todo!(),
    //         Pat::List(_) => todo!(),
    //         Pat::Ctor(_) => todo!(),
    //         Pat::Or(_) => todo!(),
    //         Pat::If(_) => todo!(),
    //     })
    // }

    // fn traverse_term_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     term_id: TermId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     match (state.f)(&mut state.accumulator, term_id.into())? {
    //         ControlFlow::Continue(()) =>
    // self.traverse_term_children_impl(term_id, state),
    //         ControlFlow::Break(()) => Ok(()),
    //     }
    // }

    // fn traverse_ty_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     ty_id: TyId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     match (state.f)(&mut state.accumulator, ty_id.into())? {
    //         ControlFlow::Continue(()) => self.traverse_ty_children_impl(ty_id,
    // state),         ControlFlow::Break(()) => Ok(()),
    //     }
    // }

    // fn traverse_pat_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     pat_id: PatId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     match (state.f)(&mut state.accumulator, pat_id.into())? {
    //         ControlFlow::Continue(()) => self.traverse_pat_children_impl(pat_id,
    // state),         ControlFlow::Break(()) => Ok(()),
    //     }
    // }

    // fn traverse_fn_def_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     fn_def_id: FnDefId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     match (state.f)(&mut state.accumulator, fn_def_id.into())? {
    //         ControlFlow::Continue(()) => self.map_fn_def(fn_def_id, |fn_def| {
    //             self.traverse_def_params_impl(fn_def.params, state)?;
    //             self.traverse_def_args_impl(fn_def.args, state)?;
    //             self.traverse_def_pat_args_impl(fn_def.pat_args, state)?;
    //             self.traverse_ty_impl(fn_def.ret_ty, state)?;
    //             self.traverse_term_impl(fn_def.body, state)?;
    //             Ok(())
    //         }),
    //         ControlFlow::Break(()) => Ok(()),
    //     }
    // }

    // fn traverse_term_children_impl<B, E, F: Folder<B, E>>(
    //     &self,
    //     term_id: TermId,
    //     state: &mut TraverseImplState<B, F>,
    // ) -> Result<(), E> {
    //     self.fmap_term(term_id, |term| match term {
    //         Term::Runtime(rt) => self.traverse_ty_impl(rt.term_ty, state),
    //         Term::Tuple(tu) => self.traverse_args_impl(tu.data, state),
    //         Term::Prim(prim_term) => match prim_term {
    //             PrimTerm::Lit(_) => Ok(()),
    //             PrimTerm::List(list) => self.map_term_list(list.elements, |items|
    // {                 for &item in items {
    //                     self.traverse_term_children_impl(item, state)?;
    //                 }
    //                 Ok(())
    //             }),
    //         },
    //         Term::Ctor(ctor_term) => {
    //             self.traverse_def_args_impl(ctor_term.data_args, state)?;
    //             self.traverse_def_args_impl(ctor_term.ctor_args, state)?;
    //             Ok(())
    //         }
    //         Term::FnCall(fn_call_term) => {
    //             self.traverse_term_children_impl(fn_call_term.subject, state)?;
    //             self.traverse_args_impl(fn_call_term.args, state)?;
    //             Ok(())
    //         }
    //         Term::FnRef(fn_def_id) => Ok(()),
    //         Term::Block(_) => todo!(),
    //         Term::Var(_) => todo!(),
    //         Term::Loop(_) => todo!(),
    //         Term::LoopControl(_) => todo!(),
    //         Term::Match(_) => todo!(),
    //         Term::Return(_) => todo!(),
    //         Term::DeclStackMember(_) => todo!(),
    //         Term::Assign(_) => todo!(),
    //         Term::Unsafe(_) => todo!(),
    //         Term::Access(_) => todo!(),
    //         Term::Cast(_) => todo!(),
    //         Term::TypeOf(_) => todo!(),
    //         Term::Ty(_) => todo!(),
    //         Term::Ref(_) => todo!(),
    //         Term::Deref(_) => todo!(),
    //         Term::Hole(_) => todo!(),
    //         Term::HoleBinder(_) => todo!(),
    //     })
    // }
}
