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

pub trait Modifier<E> = FnMut(Atom) -> Result<ControlFlow<()>, E> + Copy;

pub trait Mapper<E> = Fn(Atom) -> Result<ControlFlow<Atom>, E> + Copy;

impl<'env> TraversingUtils<'env> {
    pub fn traverse_map_atom<E, F: Mapper<E>>(&self, atom: Atom, f: F) -> Result<Atom, E> {
        match atom {
            Atom::Term(term_id) => Ok(Atom::Term(self.traverse_map_term(term_id, f)?)),
            Atom::Ty(ty_id) => Ok(Atom::Ty(self.traverse_map_ty(ty_id, f)?)),
            Atom::FnDef(fn_def_id) => Ok(Atom::FnDef(self.traverse_map_fn_def(fn_def_id, f)?)),
            Atom::Pat(pat_id) => Ok(Atom::Pat(self.traverse_map_pat(pat_id, f)?)),
        }
    }

    pub fn traverse_map_term<E, F: Mapper<E>>(&self, term_id: TermId, f: F) -> Result<TermId, E> {
        match f(term_id.into())? {
            ControlFlow::Break(atom) => Ok(TermId::try_from(atom).unwrap()),
            ControlFlow::Continue(()) => match self.get_term(term_id) {
                Term::Runtime(rt_term) => {
                    let term_ty = self.traverse_map_ty(rt_term.term_ty, f)?;
                    Ok(self.new_term(RuntimeTerm { term_ty }))
                }
                Term::Tuple(tuple_term) => {
                    let data = self.traverse_map_args(tuple_term.data, f)?;
                    Ok(self.new_term(Term::Tuple(TupleTerm { data })))
                }
                Term::Prim(prim_term) => match prim_term {
                    PrimTerm::Lit(lit) => Ok(self.new_term(Term::Prim(PrimTerm::Lit(lit)))),
                    PrimTerm::List(list_ctor) => {
                        let elements = self.traverse_map_term_list(list_ctor.elements, f)?;
                        Ok(self.new_term(Term::Prim(PrimTerm::List(ListCtor { elements }))))
                    }
                },
                Term::Ctor(ctor_term) => {
                    let data_args = self.traverse_map_def_args(ctor_term.data_args, f)?;
                    let ctor_args = self.traverse_map_def_args(ctor_term.ctor_args, f)?;
                    Ok(self.new_term(CtorTerm { ctor: ctor_term.ctor, data_args, ctor_args }))
                }
                Term::FnCall(fn_call_term) => {
                    let subject = self.traverse_map_term(fn_call_term.subject, f)?;
                    let args = self.traverse_map_args(fn_call_term.args, f)?;
                    Ok(self.new_term(FnCallTerm { args, subject, implicit: fn_call_term.implicit }))
                }
                Term::FnRef(fn_def_id) => {
                    let fn_def_id = self.traverse_map_fn_def(fn_def_id, f)?;
                    Ok(self.new_term(Term::FnRef(fn_def_id)))
                }
                Term::Block(block_term) => {
                    let statements = self.traverse_map_term_list(block_term.statements, f)?;
                    let return_value = self.traverse_map_term(block_term.return_value, f)?;
                    Ok(self.new_term(BlockTerm { statements, return_value }))
                }
                Term::Var(var_term) => Ok(self.new_term(var_term)),
                Term::Loop(loop_term) => {
                    let statements = self.traverse_map_term_list(loop_term.block.statements, f)?;
                    let return_value = self.traverse_map_term(loop_term.block.return_value, f)?;
                    Ok(self.new_term(LoopTerm { block: BlockTerm { statements, return_value } }))
                }
                Term::LoopControl(loop_control_term) => Ok(self.new_term(loop_control_term)),
                Term::Match(match_term) => {
                    let subject = self.traverse_map_term(match_term.subject, f)?;
                    let cases = self.traverse_map_pat_list(match_term.cases, f)?;
                    let decisions = self.traverse_map_term_list(match_term.decisions, f)?;
                    Ok(self.new_term(MatchTerm { cases, decisions, subject }))
                }
                Term::Return(return_term) => {
                    let expression = self.traverse_map_term(return_term.expression, f)?;
                    Ok(self.new_term(ReturnTerm { expression }))
                }
                Term::DeclStackMember(decl_stack_member_term) => {
                    let bind_pat = self.traverse_map_pat(decl_stack_member_term.bind_pat, f)?;
                    let ty = self.traverse_map_ty(decl_stack_member_term.ty, f)?;
                    let value = decl_stack_member_term
                        .value
                        .map(|v| self.traverse_map_term(v, f))
                        .transpose()?;
                    Ok(self.new_term(DeclStackMemberTerm { ty, bind_pat, value }))
                }
                Term::Assign(assign_term) => {
                    let subject = self.traverse_map_term(assign_term.subject, f)?;
                    let value = self.traverse_map_term(assign_term.value, f)?;
                    Ok(self.new_term(AssignTerm { subject, value }))
                }
                Term::Unsafe(unsafe_term) => {
                    let inner = self.traverse_map_term(unsafe_term.inner, f)?;
                    Ok(self.new_term(UnsafeTerm { inner }))
                }
                Term::Access(access_term) => {
                    let subject = self.traverse_map_term(access_term.subject, f)?;
                    Ok(self.new_term(AccessTerm { subject, field: access_term.field }))
                }
                Term::Cast(cast_term) => {
                    let subject_term = self.traverse_map_term(cast_term.subject_term, f)?;
                    let target_ty = self.traverse_map_ty(cast_term.target_ty, f)?;
                    Ok(self.new_term(CastTerm { subject_term, target_ty }))
                }
                Term::TypeOf(type_of_term) => {
                    let term = self.traverse_map_term(type_of_term.term, f)?;
                    Ok(self.new_term(TypeOfTerm { term }))
                }
                Term::Ty(ty) => {
                    let ty = self.traverse_map_ty(ty, f)?;
                    Ok(self.new_term(ty))
                }
                Term::Ref(ref_term) => {
                    let subject = self.traverse_map_term(ref_term.subject, f)?;
                    Ok(self.new_term(RefTerm {
                        subject,
                        kind: ref_term.kind,
                        mutable: ref_term.mutable,
                    }))
                }
                Term::Deref(deref_term) => {
                    let subject = self.traverse_map_term(deref_term.subject, f)?;
                    Ok(self.new_term(DerefTerm { subject }))
                }
                Term::Hole(hole_term) => Ok(self.new_term(hole_term)),
                Term::HoleBinder(hole_binder) => match hole_binder.kind {
                    HoleBinderKind::Hole(ty) => {
                        let ty = self.traverse_map_ty(ty, f)?;
                        let inner = self.traverse_map_term(hole_binder.inner, f)?;
                        Ok(self.new_term(HoleBinder {
                            hole: hole_binder.hole,
                            inner,
                            kind: HoleBinderKind::Hole(ty),
                        }))
                    }
                    HoleBinderKind::Guess(guess) => {
                        let guess = self.traverse_map_term(guess, f)?;
                        let inner = self.traverse_map_term(hole_binder.inner, f)?;
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

    pub fn traverse_map_ty<E, F: Mapper<E>>(&self, ty_id: TyId, f: F) -> Result<TyId, E> {
        match f(ty_id.into())? {
            ControlFlow::Break(ty) => Ok(TyId::try_from(ty).unwrap()),
            ControlFlow::Continue(()) => match self.get_ty(ty_id) {
                Ty::Eval(eval_term) => {
                    let eval_term = self.traverse_map_term(eval_term, f)?;
                    Ok(self.new_ty(eval_term))
                }
                Ty::Hole(hole_ty) => Ok(self.new_ty(hole_ty)),
                Ty::Var(var_ty) => Ok(self.new_ty(var_ty)),
                Ty::Tuple(tuple_ty) => {
                    let data = self.traverse_map_params(tuple_ty.data, f)?;
                    Ok(self.new_ty(TupleTy { data }))
                }
                Ty::Fn(fn_ty) => {
                    let params = self.traverse_map_params(fn_ty.params, f)?;
                    let return_ty = self.traverse_map_ty(fn_ty.return_ty, f)?;
                    Ok(self.new_ty(FnTy {
                        params,
                        return_ty,
                        implicit: fn_ty.implicit,
                        is_unsafe: fn_ty.is_unsafe,
                        pure: fn_ty.pure,
                    }))
                }
                Ty::Ref(ref_ty) => {
                    let ty = self.traverse_map_ty(ref_ty.ty, f)?;
                    Ok(self.new_ty(RefTy { ty, kind: ref_ty.kind, mutable: ref_ty.mutable }))
                }
                Ty::Data(data_ty) => {
                    let args = self.traverse_map_def_args(data_ty.args, f)?;
                    Ok(self.new_ty(DataTy { args, data_def: data_ty.data_def }))
                }
                Ty::Universe(universe_ty) => Ok(self.new_ty(universe_ty)),
            },
        }
    }

    pub fn traverse_map_pat<E, F: Mapper<E>>(&self, pat_id: PatId, f: F) -> Result<PatId, E> {
        match f(pat_id.into())? {
            ControlFlow::Break(pat) => Ok(PatId::try_from(pat).unwrap()),
            ControlFlow::Continue(()) => match self.get_pat(pat_id) {
                Pat::Binding(binding_pat) => Ok(self.new_pat(binding_pat)),
                Pat::Range(range_pat) => Ok(self.new_pat(range_pat)),
                Pat::Lit(lit_pat) => Ok(self.new_pat(lit_pat)),
                Pat::Tuple(tuple_pat) => {
                    let data = self.traverse_map_pat_args(tuple_pat.data, f)?;
                    Ok(self.new_pat(TuplePat { data_spread: tuple_pat.data_spread, data }))
                }
                Pat::List(list_pat) => {
                    let pats = self.traverse_map_pat_list(list_pat.pats, f)?;
                    Ok(self.new_pat(ListPat { spread: list_pat.spread, pats }))
                }
                Pat::Ctor(ctor_pat) => {
                    let data_args = self.traverse_map_def_args(ctor_pat.data_args, f)?;
                    let ctor_pat_args =
                        self.traverse_map_def_pat_args(ctor_pat.ctor_pat_args, f)?;
                    Ok(self.new_pat(CtorPat { data_args, ctor_pat_args, ctor: ctor_pat.ctor }))
                }
                Pat::Or(or_pat) => {
                    let alternatives = self.traverse_map_pat_list(or_pat.alternatives, f)?;
                    Ok(self.new_pat(OrPat { alternatives }))
                }
                Pat::If(if_pat) => {
                    let pat = self.traverse_map_pat(if_pat.pat, f)?;
                    let condition = self.traverse_map_term(if_pat.condition, f)?;
                    Ok(self.new_pat(IfPat { pat, condition }))
                }
            },
        }
    }

    pub fn traverse_map_term_list<E, F: Mapper<E>>(
        &self,
        term_list: TermListId,
        f: F,
    ) -> Result<TermListId, E> {
        self.map_term_list(term_list, |term_list| {
            let mut new_list = Vec::with_capacity(term_list.len());
            for term_id in term_list {
                new_list.push(self.traverse_map_term(*term_id, f)?);
            }
            Ok(self.new_term_list(new_list))
        })
    }

    pub fn traverse_map_pat_list<E, F: Mapper<E>>(
        &self,
        pat_list: PatListId,
        f: F,
    ) -> Result<PatListId, E> {
        self.map_pat_list(pat_list, |pat_list| {
            let mut new_list = Vec::with_capacity(pat_list.len());
            for pat_id in pat_list {
                new_list.push(self.traverse_map_pat(*pat_id, f)?);
            }
            Ok(self.new_pat_list(new_list))
        })
    }

    pub fn traverse_map_params<E, F: Mapper<E>>(
        &self,
        params_id: ParamsId,
        f: F,
    ) -> Result<ParamsId, E> {
        self.map_params(params_id, |params| {
            let mut new_params = Vec::with_capacity(params.len());
            for param in params {
                new_params
                    .push(ParamData { name: param.name, ty: self.traverse_map_ty(param.ty, f)? });
            }
            Ok(self.param_utils().create_params(new_params.into_iter()))
        })
    }

    pub fn traverse_map_args<E, F: Mapper<E>>(&self, args_id: ArgsId, f: F) -> Result<ArgsId, E> {
        self.map_args(args_id, |args| {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                new_args.push(ArgData {
                    target: arg.target,
                    value: self.traverse_map_term(arg.value, f)?,
                });
            }
            Ok(self.param_utils().create_args(new_args.into_iter()))
        })
    }

    pub fn traverse_map_def_args<E, F: Mapper<E>>(
        &self,
        def_args_id: DefArgsId,
        f: F,
    ) -> Result<DefArgsId, E> {
        self.map_def_args(def_args_id, |def_args| {
            let mut new_args = Vec::with_capacity(def_args.len());
            for def_arg in def_args {
                new_args.push(DefArgGroupData {
                    args: self.traverse_map_args(def_arg.args, f)?,
                    implicit: def_arg.implicit,
                });
            }
            Ok(self.param_utils().create_def_args(new_args.into_iter()))
        })
    }

    pub fn traverse_map_def_params<E, F: Mapper<E>>(
        &self,
        def_params_id: DefParamsId,
        f: F,
    ) -> Result<DefParamsId, E> {
        self.map_def_params(def_params_id, |def_params| {
            let mut new_params = Vec::with_capacity(def_params.len());
            for def_param in def_params {
                new_params.push(DefParamGroupData {
                    implicit: def_param.implicit,
                    params: self.traverse_map_params(def_param.params, f)?,
                });
            }
            Ok(self.param_utils().create_def_params(new_params.into_iter()))
        })
    }

    pub fn traverse_map_pat_args<E, F: Mapper<E>>(
        &self,
        pat_args_id: PatArgsId,
        f: F,
    ) -> Result<PatArgsId, E> {
        self.map_pat_args(pat_args_id, |pat_args| {
            let mut new_args = Vec::with_capacity(pat_args.len());
            for pat_arg in pat_args {
                new_args.push(PatArgData {
                    target: pat_arg.target,
                    pat: self.traverse_map_pat(pat_arg.pat, f)?,
                });
            }
            Ok(self.param_utils().create_pat_args(new_args.into_iter()))
        })
    }

    pub fn traverse_map_def_pat_args<E, F: Mapper<E>>(
        &self,
        def_pat_args_id: DefPatArgsId,
        f: F,
    ) -> Result<DefPatArgsId, E> {
        self.map_def_pat_args(def_pat_args_id, |def_pat_args| {
            let mut new_args = Vec::with_capacity(def_pat_args.len());
            for def_pat_arg in def_pat_args {
                new_args.push(DefPatArgGroupData {
                    pat_args: self.traverse_map_pat_args(def_pat_arg.pat_args, f)?,
                    spread: def_pat_arg.spread,
                    implicit: def_pat_arg.implicit,
                });
            }
            Ok(self.param_utils().create_def_pat_args(new_args.into_iter()))
        })
    }

    pub fn traverse_map_fn_def<E, F: Mapper<E>>(
        &self,
        fn_def_id: FnDefId,
        f: F,
    ) -> Result<FnDefId, E> {
        match f(fn_def_id.into())? {
            ControlFlow::Break(fn_def_id) => Ok(FnDefId::try_from(fn_def_id).unwrap()),
            ControlFlow::Continue(()) => {
                let fn_def = self.get_fn_def(fn_def_id);
                Ok(self.fn_utils().create_fn_def(FnDefData {
                    name: fn_def.name,
                    ty: {
                        let fn_ty = fn_def.ty;
                        FnTy {
                            params: self.traverse_map_params(fn_ty.params, f)?,
                            return_ty: self.traverse_map_ty(fn_ty.return_ty, f)?,
                            implicit: fn_ty.implicit,
                            is_unsafe: fn_ty.is_unsafe,
                            pure: fn_ty.pure,
                        }
                    },
                    body: match fn_def.body {
                        FnBody::Defined(defined) => {
                            FnBody::Defined(self.traverse_map_term(defined, f)?)
                        }
                        FnBody::Intrinsic(_) | FnBody::Axiom => fn_def.body, // no-op
                    },
                }))
            }
        }
    }

    pub fn traverse_modify_term<E, F: Modifier<E>>(
        &self,
        term_id: TermId,
        f: &mut F,
    ) -> Result<(), E> {
        match f(term_id.into())? {
            ControlFlow::Break(_) => Ok(()),
            ControlFlow::Continue(()) => match self.get_term(term_id) {
                Term::Runtime(rt_term) => self.traverse_modify_ty(rt_term.term_ty, f),
                Term::Tuple(tuple_term) => self.traverse_modify_args(tuple_term.data, f),
                Term::Prim(prim_term) => match prim_term {
                    PrimTerm::Lit(_) => Ok(()),
                    PrimTerm::List(list_ctor) => {
                        self.traverse_modify_term_list(list_ctor.elements, f)
                    }
                },
                Term::Ctor(ctor_term) => {
                    self.traverse_modify_def_args(ctor_term.data_args, f)?;
                    self.traverse_modify_def_args(ctor_term.ctor_args, f)
                }
                Term::FnCall(fn_call_term) => {
                    self.traverse_modify_term(fn_call_term.subject, f)?;
                    self.traverse_modify_args(fn_call_term.args, f)
                }
                Term::FnRef(fn_def_id) => self.traverse_modify_fn_def(fn_def_id, f),
                Term::Block(block_term) => {
                    self.traverse_modify_term_list(block_term.statements, f)?;
                    self.traverse_modify_term(block_term.return_value, f)
                }
                Term::Var(_) => Ok(()),
                Term::Loop(loop_term) => {
                    self.traverse_modify_term_list(loop_term.block.statements, f)?;
                    self.traverse_modify_term(loop_term.block.return_value, f)
                }
                Term::LoopControl(_) => Ok(()),
                Term::Match(match_term) => {
                    self.traverse_modify_term(match_term.subject, f)?;
                    self.traverse_modify_pat_list(match_term.cases, f)?;
                    self.traverse_modify_term_list(match_term.decisions, f)
                }
                Term::Return(return_term) => self.traverse_modify_term(return_term.expression, f),
                Term::DeclStackMember(decl_stack_member_term) => {
                    self.traverse_modify_pat(decl_stack_member_term.bind_pat, f)?;
                    self.traverse_modify_ty(decl_stack_member_term.ty, f)?;
                    let (Some(()) | None) = decl_stack_member_term
                        .value
                        .map(|v| self.traverse_modify_term(v, f))
                        .transpose()?;
                    Ok(())
                }
                Term::Assign(assign_term) => {
                    self.traverse_modify_term(assign_term.subject, f)?;
                    self.traverse_modify_term(assign_term.value, f)
                }
                Term::Unsafe(unsafe_term) => self.traverse_modify_term(unsafe_term.inner, f),
                Term::Access(access_term) => self.traverse_modify_term(access_term.subject, f),
                Term::Cast(cast_term) => {
                    self.traverse_modify_term(cast_term.subject_term, f)?;
                    self.traverse_modify_ty(cast_term.target_ty, f)
                }
                Term::TypeOf(type_of_term) => self.traverse_modify_term(type_of_term.term, f),
                Term::Ty(ty) => self.traverse_modify_ty(ty, f),
                Term::Ref(ref_term) => self.traverse_modify_term(ref_term.subject, f),
                Term::Deref(deref_term) => self.traverse_modify_term(deref_term.subject, f),
                Term::Hole(_) => Ok(()),
                Term::HoleBinder(hole_binder) => match hole_binder.kind {
                    HoleBinderKind::Hole(ty) => {
                        self.traverse_modify_ty(ty, f)?;
                        self.traverse_modify_term(hole_binder.inner, f)
                    }
                    HoleBinderKind::Guess(guess) => {
                        self.traverse_modify_term(guess, f)?;
                        self.traverse_modify_term(hole_binder.inner, f)
                    }
                },
            },
        }
    }

    pub fn traverse_modify_ty<E, F: Modifier<E>>(&self, ty_id: TyId, f: &mut F) -> Result<(), E> {
        match f(ty_id.into())? {
            ControlFlow::Break(_) => Ok(()),
            ControlFlow::Continue(()) => match self.get_ty(ty_id) {
                Ty::Eval(eval_term) => self.traverse_modify_term(eval_term, f),
                Ty::Tuple(tuple_ty) => self.traverse_modify_params(tuple_ty.data, f),
                Ty::Fn(fn_ty) => {
                    self.traverse_modify_params(fn_ty.params, f)?;
                    self.traverse_modify_ty(fn_ty.return_ty, f)
                }
                Ty::Ref(ref_ty) => self.traverse_modify_ty(ref_ty.ty, f),
                Ty::Data(data_ty) => self.traverse_modify_def_args(data_ty.args, f),
                Ty::Universe(_) | Ty::Var(_) | Ty::Hole(_) => Ok(()),
            },
        }
    }

    pub fn traverse_modify_pat<E, F: Modifier<E>>(
        &self,
        pat_id: PatId,
        f: &mut F,
    ) -> Result<(), E> {
        match f(pat_id.into())? {
            ControlFlow::Break(()) => Ok(()),
            ControlFlow::Continue(()) => match self.get_pat(pat_id) {
                Pat::Binding(_) | Pat::Range(_) | Pat::Lit(_) => Ok(()),
                Pat::Tuple(tuple_pat) => self.traverse_modify_pat_args(tuple_pat.data, f),
                Pat::List(list_pat) => self.traverse_modify_pat_list(list_pat.pats, f),
                Pat::Ctor(ctor_pat) => {
                    self.traverse_modify_def_args(ctor_pat.data_args, f)?;

                    self.traverse_modify_def_pat_args(ctor_pat.ctor_pat_args, f)
                }
                Pat::Or(or_pat) => self.traverse_modify_pat_list(or_pat.alternatives, f),
                Pat::If(if_pat) => self.traverse_modify_pat(if_pat.pat, f),
            },
        }
    }

    pub fn traverse_modify_fn_def<E, F: Modifier<E>>(
        &self,
        fn_def_id: FnDefId,
        f: &mut F,
    ) -> Result<(), E> {
        match f(fn_def_id.into())? {
            ControlFlow::Break(()) => Ok(()),
            ControlFlow::Continue(()) => {
                let fn_def = self.get_fn_def(fn_def_id);
                let fn_ty = fn_def.ty;
                self.traverse_modify_params(fn_ty.params, f)?;
                self.traverse_modify_ty(fn_ty.return_ty, f)?;

                match fn_def.body {
                    FnBody::Defined(defined) => self.traverse_modify_term(defined, f),
                    FnBody::Intrinsic(_) | FnBody::Axiom => Ok(()),
                }
            }
        }
    }

    pub fn traverse_modify_atom<E, F: Modifier<E>>(&self, atom: Atom, f: &mut F) -> Result<(), E> {
        match atom {
            Atom::Term(term_id) => self.traverse_modify_term(term_id, f),
            Atom::Ty(ty_id) => self.traverse_modify_ty(ty_id, f),
            Atom::FnDef(fn_def_id) => self.traverse_modify_fn_def(fn_def_id, f),
            Atom::Pat(pat_id) => self.traverse_modify_pat(pat_id, f),
        }
    }

    pub fn traverse_modify_term_list<E, F: Modifier<E>>(
        &self,
        term_list_id: TermListId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_term_list(term_list_id, |term_list| {
            for &term in term_list {
                self.traverse_modify_term(term, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_pat_list<E, F: Modifier<E>>(
        &self,
        pat_list_id: PatListId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_pat_list(pat_list_id, |pat_list| {
            for &pat in pat_list {
                self.traverse_modify_pat(pat, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_params<E, F: Modifier<E>>(
        &self,
        params_id: ParamsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_params(params_id, |params| {
            for &param in params {
                self.traverse_modify_ty(param.ty, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_def_pat_args<E, F: Modifier<E>>(
        &self,
        def_pat_args_id: DefPatArgsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_def_pat_args(def_pat_args_id, |def_pat_args| {
            for &pat_arg_group in def_pat_args {
                self.traverse_modify_pat_args(pat_arg_group.pat_args, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_pat_args<E, F: Modifier<E>>(
        &self,
        pat_args_id: PatArgsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_pat_args(pat_args_id, |pat_args| {
            for &arg in pat_args {
                self.traverse_modify_pat(arg.pat, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_args<E, F: Modifier<E>>(
        &self,
        args_id: ArgsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_args(args_id, |args| {
            for &arg in args {
                self.traverse_modify_term(arg.value, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_def_args<E, F: Modifier<E>>(
        &self,
        def_args_id: DefArgsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_def_args(def_args_id, |def_args| {
            for &arg_group in def_args {
                self.traverse_modify_args(arg_group.args, f)?;
            }
            Ok(())
        })
    }

    pub fn traverse_modify_def_params<E, F: Modifier<E>>(
        &self,
        def_params_id: DefParamsId,
        f: &mut F,
    ) -> Result<(), E> {
        self.map_def_params(def_params_id, |def_params| {
            for &param_group in def_params {
                self.traverse_modify_params(param_group.params, f)?;
            }
            Ok(())
        })
    }
}
