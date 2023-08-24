//! Utilities to traverse the TIR.
use core::fmt;
use std::{cell::RefCell, collections::HashSet, ops::ControlFlow};

use derive_more::{From, TryInto};
use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};

use crate::{
    access::AccessTerm,
    args::{Arg, ArgsId, PatArg, PatArgsId, PatOrCapture},
    arrays::{ArrayPat, ArrayTerm, IndexTerm},
    casting::CastTerm,
    control::{IfPat, LoopTerm, MatchCase, MatchTerm, OrPat, ReturnTerm},
    data::{CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataDefId, DataTy, PrimitiveCtorInfo},
    environment::{env::Env, stores::tir_stores},
    fns::{FnBody, FnCallTerm, FnDef, FnDefId, FnTy},
    locations::LocationTarget,
    mods::{ModDefId, ModMemberId, ModMemberValue},
    node,
    params::{Param, ParamsId},
    pats::{Pat, PatId, PatListId},
    refs::{DerefTerm, RefTerm, RefTy},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    terms::{Term, TermId, TermListId, UnsafeTerm},
    tuples::{TuplePat, TupleTerm, TupleTy},
    tys::{Ty, TyId, TypeOfTerm},
};

/// Contains methods to traverse the Hash TIR structure.
pub struct TraversingUtils {
    visited: RefCell<HashSet<Atom>>,
    visit_fns_once: bool,
}

/// An atom in the TIR.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, From, TryInto)]
pub enum Atom {
    Term(TermId),
    Ty(TyId),
    FnDef(FnDefId),
    Pat(PatId),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Term(term_id) => write!(f, "{}", term_id),
            Atom::Ty(ty_id) => write!(f, "{}", ty_id),
            Atom::FnDef(fn_def_id) => write!(f, "{}", fn_def_id),
            Atom::Pat(pat_id) => write!(f, "{}", pat_id),
        }
    }
}

impl From<Atom> for LocationTarget {
    fn from(atom: Atom) -> Self {
        match atom {
            Atom::Term(term_id) => Self::Term(term_id),
            Atom::Ty(ty_id) => Self::Ty(ty_id),
            Atom::FnDef(fn_def_id) => Self::FnDef(fn_def_id),
            Atom::Pat(pat_id) => Self::Pat(pat_id),
        }
    }
}

/// Function to visit an atom.
///
/// This does not return a value, but instead returns a `ControlFlow` to
/// indicate whether to continue or break the traversal.
pub trait Visitor<E> = FnMut(Atom) -> Result<ControlFlow<()>, E>;

/// Function to map an atom to another atom.
///
/// This returns a `ControlFlow` to indicate whether to continue by duplicating
/// the atom canonically or break the traversal with a custom atom.
pub trait Mapper<E> = Fn(Atom) -> Result<ControlFlow<Atom>, E> + Copy;

/// Contains the implementation of `fmap` and `visit` for each atom, as well as
/// secondary components such as arguments and parameters.
impl TraversingUtils {
    /// Create a new `TraversingUtils`.
    ///
    /// The `env` parameter is needed for the `utils` macro
    pub fn new(_: &Env) -> Self {
        Self { visited: RefCell::new(HashSet::new()), visit_fns_once: true }
    }

    pub fn set_visit_fns_once(&mut self, visit_fns_once: bool) {
        self.visit_fns_once = visit_fns_once;
    }

    pub fn fmap_atom_non_preserving<E, F: Mapper<E>>(&self, atom: Atom, f: F) -> Result<Atom, E> {
        match f(atom)? {
            ControlFlow::Continue(()) => self.fmap_atom(atom, f),
            ControlFlow::Break(atom) => Ok(atom),
        }
    }

    pub fn fmap_atom<E, F: Mapper<E>>(&self, atom: Atom, f: F) -> Result<Atom, E> {
        match atom {
            Atom::Term(term_id) => Ok(Atom::Term(self.fmap_term(term_id, f)?)),
            Atom::Ty(ty_id) => Ok(Atom::Ty(self.fmap_ty(ty_id, f)?)),
            Atom::FnDef(fn_def_id) => Ok(Atom::FnDef(self.fmap_fn_def(fn_def_id, f)?)),
            Atom::Pat(pat_id) => Ok(Atom::Pat(self.fmap_pat(pat_id, f)?)),
        }
    }

    pub fn fmap_term<E, F: Mapper<E>>(&self, term_id: TermId, f: F) -> Result<TermId, E> {
        let result = match f(term_id.into())? {
            ControlFlow::Break(atom) => match atom {
                Atom::Term(t) => Ok(t),
                Atom::Ty(ty) => Ok(ty.as_term()),
                Atom::FnDef(fn_def_id) => Ok(Term::from(fn_def_id)),
                Atom::Pat(_) => unreachable!("cannot use a pattern as a term"),
            },
            ControlFlow::Continue(()) => match *term_id.value() {
                Term::Tuple(tuple_term) => {
                    let data = self.fmap_args(tuple_term.data, f)?;
                    Ok(Term::from(Term::Tuple(TupleTerm { data })))
                }
                Term::Lit(lit) => Ok(Term::from(Term::Lit(lit))),
                Term::Array(list_ctor) => {
                    let elements = self.fmap_term_list(list_ctor.elements, f)?;
                    Ok(Term::from(Term::Array(ArrayTerm { elements })))
                }
                Term::Ctor(ctor_term) => {
                    let data_args = self.fmap_args(ctor_term.data_args, f)?;
                    let ctor_args = self.fmap_args(ctor_term.ctor_args, f)?;
                    Ok(Term::from(CtorTerm { ctor: ctor_term.ctor, data_args, ctor_args }))
                }
                Term::FnCall(fn_call_term) => {
                    let subject = self.fmap_term(fn_call_term.subject, f)?;
                    let args = self.fmap_args(fn_call_term.args, f)?;
                    Ok(Term::from(FnCallTerm { args, subject, implicit: fn_call_term.implicit }))
                }
                Term::FnRef(fn_def_id) => {
                    let fn_def_id = self.fmap_fn_def(fn_def_id, f)?;
                    Ok(Term::from(Term::FnRef(fn_def_id)))
                }
                Term::Block(block_term) => {
                    let statements = self.fmap_term_list(block_term.statements, f)?;
                    let return_value = self.fmap_term(block_term.return_value, f)?;
                    Ok(Term::from(BlockTerm {
                        statements,
                        return_value,
                        stack_id: block_term.stack_id,
                    }))
                }
                Term::Var(var_term) => Ok(Term::from(var_term)),
                Term::Loop(loop_term) => {
                    let statements = self.fmap_term_list(loop_term.block.statements, f)?;
                    let return_value = self.fmap_term(loop_term.block.return_value, f)?;
                    Ok(Term::from(LoopTerm {
                        block: BlockTerm {
                            statements,
                            return_value,
                            stack_id: loop_term.block.stack_id,
                        },
                    }))
                }
                Term::LoopControl(loop_control_term) => Ok(Term::from(loop_control_term)),
                Term::Match(match_term) => {
                    let subject = self.fmap_term(match_term.subject, f)?;

                    let cases = MatchCase::seq_data(
                        match_term
                            .cases
                            .value()
                            .iter()
                            .map(|case| {
                                let bind_pat = self.fmap_pat(case.bind_pat, f)?;
                                let value = self.fmap_term(case.value, f)?;
                                Ok(MatchCase { bind_pat, value, stack_id: case.stack_id })
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    Ok(Term::from(MatchTerm { cases, subject, origin: match_term.origin }))
                }
                Term::Return(return_term) => {
                    let expression = self.fmap_term(return_term.expression, f)?;
                    Ok(Term::from(ReturnTerm { expression }))
                }
                Term::Decl(decl_stack_member_term) => {
                    let bind_pat = self.fmap_pat(decl_stack_member_term.bind_pat, f)?;
                    let ty = self.fmap_ty(decl_stack_member_term.ty, f)?;
                    let value =
                        decl_stack_member_term.value.map(|v| self.fmap_term(v, f)).transpose()?;
                    Ok(Term::from(DeclTerm { ty, bind_pat, value }))
                }
                Term::Assign(assign_term) => {
                    let subject = self.fmap_term(assign_term.subject, f)?;
                    let value = self.fmap_term(assign_term.value, f)?;
                    Ok(Term::from(AssignTerm { subject, value }))
                }
                Term::Unsafe(unsafe_term) => {
                    let inner = self.fmap_term(unsafe_term.inner, f)?;
                    Ok(Term::from(UnsafeTerm { inner }))
                }
                Term::Access(access_term) => {
                    let subject = self.fmap_term(access_term.subject, f)?;
                    Ok(Term::from(AccessTerm { subject, field: access_term.field }))
                }
                Term::Index(index_term) => {
                    let subject = self.fmap_term(index_term.subject, f)?;
                    let index = self.fmap_term(index_term.index, f)?;
                    Ok(Term::from(IndexTerm { subject, index }))
                }
                Term::Cast(cast_term) => {
                    let subject_term = self.fmap_term(cast_term.subject_term, f)?;
                    let target_ty = self.fmap_ty(cast_term.target_ty, f)?;
                    Ok(Term::from(CastTerm { subject_term, target_ty }))
                }
                Term::TypeOf(type_of_term) => {
                    let term = self.fmap_term(type_of_term.term, f)?;
                    Ok(Term::from(TypeOfTerm { term }))
                }
                Term::Ty(ty) => {
                    let ty = self.fmap_ty(ty, f)?;
                    Ok(Term::from(ty))
                }
                Term::Ref(ref_term) => {
                    let subject = self.fmap_term(ref_term.subject, f)?;
                    Ok(Term::from(RefTerm {
                        subject,
                        kind: ref_term.kind,
                        mutable: ref_term.mutable,
                    }))
                }
                Term::Deref(deref_term) => {
                    let subject = self.fmap_term(deref_term.subject, f)?;
                    Ok(Term::from(DerefTerm { subject }))
                }
                Term::Hole(hole_term) => Ok(Term::from(hole_term)),
            },
        }?;

        tir_stores().location().copy_location(term_id, result);
        Ok(result)
    }

    pub fn fmap_ty<E, F: Mapper<E>>(&self, ty_id: TyId, f: F) -> Result<TyId, E> {
        let result = match f(ty_id.into())? {
            ControlFlow::Break(ty) => match ty {
                Atom::Ty(ty) => Ok(ty),
                Atom::Term(term) => Ok(term.as_ty()),
                _ => unreachable!("got non-type in fmap_ty"),
            },
            ControlFlow::Continue(()) => match ty_id.value() {
                Ty::Eval(eval_term) => {
                    let eval_term = self.fmap_term(eval_term, f)?;
                    Ok(Ty::from(eval_term))
                }
                Ty::Hole(hole_ty) => Ok(Ty::from(hole_ty)),
                Ty::Var(var_ty) => Ok(Ty::from(var_ty)),
                Ty::Tuple(tuple_ty) => {
                    let data = self.fmap_params(tuple_ty.data, f)?;
                    Ok(Ty::from(TupleTy { data }))
                }
                Ty::Fn(fn_ty) => {
                    let params = self.fmap_params(fn_ty.params, f)?;
                    let return_ty = self.fmap_ty(fn_ty.return_ty, f)?;
                    Ok(Ty::from(FnTy {
                        params,
                        return_ty,
                        implicit: fn_ty.implicit,
                        is_unsafe: fn_ty.is_unsafe,
                        pure: fn_ty.pure,
                    }))
                }
                Ty::Ref(ref_ty) => {
                    let ty = self.fmap_ty(ref_ty.ty, f)?;
                    Ok(Ty::from(RefTy { ty, kind: ref_ty.kind, mutable: ref_ty.mutable }))
                }
                Ty::Data(data_ty) => {
                    let args = self.fmap_args(data_ty.args, f)?;
                    Ok(Ty::from(DataTy { args, data_def: data_ty.data_def }))
                }
                Ty::Universe(universe_ty) => Ok(Ty::from(universe_ty)),
            },
        }?;
        tir_stores().location().copy_location(ty_id, result);
        Ok(result)
    }

    pub fn fmap_pat<E, F: Mapper<E>>(&self, pat_id: PatId, f: F) -> Result<PatId, E> {
        let result = match f(pat_id.into())? {
            ControlFlow::Break(pat) => Ok(PatId::try_from(pat).unwrap()),
            ControlFlow::Continue(()) => match pat_id.value() {
                Pat::Binding(binding_pat) => Ok(Pat::create_from(binding_pat)),
                Pat::Range(range_pat) => Ok(Pat::create_from(range_pat)),
                Pat::Lit(lit_pat) => Ok(Pat::create_from(lit_pat)),
                Pat::Tuple(tuple_pat) => {
                    let data = self.fmap_pat_args(tuple_pat.data, f)?;
                    Ok(Pat::create_from(TuplePat { data_spread: tuple_pat.data_spread, data }))
                }
                Pat::Array(list_pat) => {
                    let pats = self.fmap_pat_list(list_pat.pats, f)?;
                    Ok(Pat::create_from(ArrayPat { spread: list_pat.spread, pats }))
                }
                Pat::Ctor(ctor_pat) => {
                    let data_args = self.fmap_args(ctor_pat.data_args, f)?;
                    let ctor_pat_args = self.fmap_pat_args(ctor_pat.ctor_pat_args, f)?;
                    Ok(Pat::create_from(CtorPat {
                        data_args,
                        ctor_pat_args,
                        ctor: ctor_pat.ctor,
                        ctor_pat_args_spread: ctor_pat.ctor_pat_args_spread,
                    }))
                }
                Pat::Or(or_pat) => {
                    let alternatives = self.fmap_pat_list(or_pat.alternatives, f)?;
                    Ok(Pat::create_from(OrPat { alternatives }))
                }
                Pat::If(if_pat) => {
                    let pat = self.fmap_pat(if_pat.pat, f)?;
                    let condition = self.fmap_term(if_pat.condition, f)?;
                    Ok(Pat::create_from(IfPat { pat, condition }))
                }
            },
        }?;
        tir_stores().location().copy_location(pat_id, result);
        Ok(result)
    }

    pub fn fmap_term_list<E, F: Mapper<E>>(
        &self,
        term_list: TermListId,
        f: F,
    ) -> Result<TermListId, E> {
        let mut new_list = Vec::with_capacity(term_list.value().len());
        for term_id in term_list.value().value() {
            new_list.push(self.fmap_term(term_id, f)?);
        }
        Ok(node!(TermId::seq_data(new_list)))
    }

    pub fn fmap_pat_list<E, F: Mapper<E>>(
        &self,
        pat_list: PatListId,
        f: F,
    ) -> Result<PatListId, E> {
        let mut new_list = Vec::with_capacity(pat_list.len());
        for pat_id in pat_list.value() {
            match pat_id {
                PatOrCapture::Pat(pat_id) => {
                    new_list.push(PatOrCapture::Pat(self.fmap_pat(pat_id, f)?));
                }
                PatOrCapture::Capture => {
                    new_list.push(PatOrCapture::Capture);
                }
            }
        }
        Ok(PatOrCapture::seq_data(new_list))
    }

    pub fn fmap_params<E, F: Mapper<E>>(&self, params_id: ParamsId, f: F) -> Result<ParamsId, E> {
        let new_params = {
            let mut new_params = Vec::with_capacity(params_id.len());
            for param in params_id.iter() {
                let param = param.value();
                new_params.push(Param {
                    name: param.name,
                    ty: self.fmap_ty(param.ty, f)?,
                    default: param.default.map(|default| self.fmap_term(default, f)).transpose()?,
                });
            }
            Ok(Param::seq_data(new_params))
        }?;

        tir_stores().location().copy_locations(params_id, new_params);
        Ok(new_params)
    }

    pub fn fmap_args<E, F: Mapper<E>>(&self, args_id: ArgsId, f: F) -> Result<ArgsId, E> {
        let mut new_args = Vec::with_capacity(args_id.len());
        for arg in args_id.value() {
            new_args.push(Arg { target: arg.target, value: self.fmap_term(arg.value, f)? });
        }
        let new_args_id = Arg::seq_data(new_args);
        tir_stores().location().copy_locations(args_id, new_args_id);
        Ok(new_args_id)
    }

    pub fn fmap_pat_args<E, F: Mapper<E>>(
        &self,
        pat_args_id: PatArgsId,
        f: F,
    ) -> Result<PatArgsId, E> {
        let new_pat_args = {
            let mut new_args = Vec::with_capacity(pat_args_id.len());
            for pat_arg in pat_args_id.iter() {
                let pat_arg = pat_arg.value();
                new_args.push(PatArg {
                    target: pat_arg.target,
                    pat: match pat_arg.pat {
                        PatOrCapture::Pat(pat_id) => PatOrCapture::Pat(self.fmap_pat(pat_id, f)?),
                        PatOrCapture::Capture => PatOrCapture::Capture,
                    },
                });
            }
            Ok(PatArg::seq_data(new_args))
        }?;

        tir_stores().location().copy_locations(pat_args_id, new_pat_args);
        Ok(new_pat_args)
    }

    pub fn fmap_fn_def<E, F: Mapper<E>>(&self, fn_def_id: FnDefId, f: F) -> Result<FnDefId, E> {
        if self.visit_fns_once {
            {
                if self.visited.borrow().contains(&fn_def_id.into()) {
                    return Ok(fn_def_id);
                }
            }
            self.visited.borrow_mut().insert(fn_def_id.into());
        }

        let new_fn_def = match f(fn_def_id.into())? {
            ControlFlow::Break(fn_def_id) => Ok(FnDefId::try_from(fn_def_id).unwrap()),
            ControlFlow::Continue(()) => {
                let fn_def = fn_def_id.value();

                match fn_def.body {
                    FnBody::Defined(defined) => {
                        let params = self.fmap_params(fn_def.ty.params, f)?;
                        let return_ty = self.fmap_ty(fn_def.ty.return_ty, f)?;
                        let body = FnBody::Defined(self.fmap_term(defined, f)?);
                        Ok(FnDef::create_with(|id| FnDef {
                            id,
                            name: fn_def.name,
                            ty: FnTy {
                                params,
                                return_ty,
                                implicit: fn_def.ty.implicit,
                                is_unsafe: fn_def.ty.is_unsafe,
                                pure: fn_def.ty.pure,
                            },
                            body,
                        }))
                    }
                    FnBody::Intrinsic(_) | FnBody::Axiom => Ok(fn_def_id),
                }
            }
        }?;

        tir_stores().location().copy_location(fn_def_id, new_fn_def);
        tir_stores().ast_info().fn_defs().copy_node(fn_def_id, new_fn_def);

        Ok(new_fn_def)
    }

    pub fn visit_term<E, F: Visitor<E>>(&self, term_id: TermId, f: &mut F) -> Result<(), E> {
        match f(term_id.into())? {
            ControlFlow::Break(_) => Ok(()),
            ControlFlow::Continue(()) => match *term_id.value() {
                Term::Tuple(tuple_term) => self.visit_args(tuple_term.data, f),
                Term::Lit(_) => Ok(()),
                Term::Array(list_ctor) => self.visit_term_list(list_ctor.elements, f),
                Term::Ctor(ctor_term) => {
                    self.visit_args(ctor_term.data_args, f)?;
                    self.visit_args(ctor_term.ctor_args, f)
                }
                Term::FnCall(fn_call_term) => {
                    self.visit_term(fn_call_term.subject, f)?;
                    self.visit_args(fn_call_term.args, f)
                }
                Term::FnRef(fn_def_id) => self.visit_fn_def(fn_def_id, f),
                Term::Block(block_term) => {
                    self.visit_term_list(block_term.statements, f)?;
                    self.visit_term(block_term.return_value, f)
                }
                Term::Var(_) => Ok(()),
                Term::Loop(loop_term) => {
                    self.visit_term_list(loop_term.block.statements, f)?;
                    self.visit_term(loop_term.block.return_value, f)
                }
                Term::LoopControl(_) => Ok(()),
                Term::Match(match_term) => {
                    self.visit_term(match_term.subject, f)?;
                    for case in match_term.cases.iter() {
                        let case = case.value();
                        self.visit_pat(case.bind_pat, f)?;
                        self.visit_term(case.value, f)?;
                    }
                    Ok(())
                }
                Term::Return(return_term) => self.visit_term(return_term.expression, f),
                Term::Decl(decl_stack_member_term) => {
                    self.visit_pat(decl_stack_member_term.bind_pat, f)?;
                    self.visit_ty(decl_stack_member_term.ty, f)?;
                    let (Some(()) | None) =
                        decl_stack_member_term.value.map(|v| self.visit_term(v, f)).transpose()?;
                    Ok(())
                }
                Term::Assign(assign_term) => {
                    self.visit_term(assign_term.subject, f)?;
                    self.visit_term(assign_term.value, f)
                }
                Term::Unsafe(unsafe_term) => self.visit_term(unsafe_term.inner, f),
                Term::Access(access_term) => self.visit_term(access_term.subject, f),
                Term::Index(index_term) => {
                    self.visit_term(index_term.subject, f)?;
                    self.visit_term(index_term.index, f)
                }
                Term::Cast(cast_term) => {
                    self.visit_term(cast_term.subject_term, f)?;
                    self.visit_ty(cast_term.target_ty, f)
                }
                Term::TypeOf(type_of_term) => self.visit_term(type_of_term.term, f),
                Term::Ty(ty) => self.visit_ty(ty, f),
                Term::Ref(ref_term) => self.visit_term(ref_term.subject, f),
                Term::Deref(deref_term) => self.visit_term(deref_term.subject, f),
                Term::Hole(_) => Ok(()),
            },
        }
    }

    pub fn visit_ty<E, F: Visitor<E>>(&self, ty_id: TyId, f: &mut F) -> Result<(), E> {
        match f(ty_id.into())? {
            ControlFlow::Break(_) => Ok(()),
            ControlFlow::Continue(()) => match ty_id.value() {
                Ty::Eval(eval_term) => self.visit_term(eval_term, f),
                Ty::Tuple(tuple_ty) => self.visit_params(tuple_ty.data, f),
                Ty::Fn(fn_ty) => {
                    self.visit_params(fn_ty.params, f)?;
                    self.visit_ty(fn_ty.return_ty, f)
                }
                Ty::Ref(ref_ty) => self.visit_ty(ref_ty.ty, f),
                Ty::Data(data_ty) => self.visit_args(data_ty.args, f),
                Ty::Universe(_) | Ty::Var(_) | Ty::Hole(_) => Ok(()),
            },
        }
    }

    pub fn visit_pat<E, F: Visitor<E>>(&self, pat_id: PatId, f: &mut F) -> Result<(), E> {
        match f(pat_id.into())? {
            ControlFlow::Break(()) => Ok(()),
            ControlFlow::Continue(()) => match pat_id.value() {
                Pat::Binding(_) | Pat::Range(_) | Pat::Lit(_) => Ok(()),
                Pat::Tuple(tuple_pat) => self.visit_pat_args(tuple_pat.data, f),
                Pat::Array(list_pat) => self.visit_pat_list(list_pat.pats, f),
                Pat::Ctor(ctor_pat) => {
                    self.visit_args(ctor_pat.data_args, f)?;
                    self.visit_pat_args(ctor_pat.ctor_pat_args, f)
                }
                Pat::Or(or_pat) => self.visit_pat_list(or_pat.alternatives, f),
                Pat::If(if_pat) => {
                    self.visit_pat(if_pat.pat, f)?;
                    self.visit_term(if_pat.condition, f)
                }
            },
        }
    }

    pub fn visit_fn_def<E, F: Visitor<E>>(&self, fn_def_id: FnDefId, f: &mut F) -> Result<(), E> {
        if self.visit_fns_once {
            {
                if self.visited.borrow().contains(&fn_def_id.into()) {
                    return Ok(());
                }
            }
            self.visited.borrow_mut().insert(fn_def_id.into());
        }

        match f(fn_def_id.into())? {
            ControlFlow::Break(()) => Ok(()),
            ControlFlow::Continue(()) => {
                let fn_def = fn_def_id.value();
                let fn_ty = fn_def.ty;
                self.visit_params(fn_ty.params, f)?;
                self.visit_ty(fn_ty.return_ty, f)?;

                match fn_def.body {
                    FnBody::Defined(defined) => self.visit_term(defined, f),
                    FnBody::Intrinsic(_) | FnBody::Axiom => Ok(()),
                }
            }
        }
    }

    pub fn visit_atom<E, F: Visitor<E>>(&self, atom: Atom, f: &mut F) -> Result<(), E> {
        match atom {
            Atom::Term(term_id) => self.visit_term(term_id, f),
            Atom::Ty(ty_id) => self.visit_ty(ty_id, f),
            Atom::FnDef(fn_def_id) => self.visit_fn_def(fn_def_id, f),
            Atom::Pat(pat_id) => self.visit_pat(pat_id, f),
        }
    }

    pub fn visit_term_list<E, F: Visitor<E>>(
        &self,
        term_list_id: TermListId,
        f: &mut F,
    ) -> Result<(), E> {
        for term in term_list_id.value().value() {
            self.visit_term(term, f)?;
        }
        Ok(())
    }

    pub fn visit_pat_list<E, F: Visitor<E>>(
        &self,
        pat_list_id: PatListId,
        f: &mut F,
    ) -> Result<(), E> {
        for pat in pat_list_id.value() {
            if let PatOrCapture::Pat(pat) = pat {
                self.visit_pat(pat, f)?;
            }
        }
        Ok(())
    }

    pub fn visit_params<E, F: Visitor<E>>(&self, params_id: ParamsId, f: &mut F) -> Result<(), E> {
        for param in params_id.iter() {
            let param = param.value();
            self.visit_ty(param.ty, f)?;
            if let Some(default) = param.default {
                self.visit_term(default, f)?;
            }
        }
        Ok(())
    }

    pub fn visit_pat_args<E, F: Visitor<E>>(
        &self,
        pat_args_id: PatArgsId,
        f: &mut F,
    ) -> Result<(), E> {
        for arg in pat_args_id.value() {
            if let PatOrCapture::Pat(pat) = arg.pat {
                self.visit_pat(pat, f)?;
            }
        }
        Ok(())
    }

    pub fn visit_args<E, F: Visitor<E>>(&self, args_id: ArgsId, f: &mut F) -> Result<(), E> {
        for arg in args_id.value() {
            self.visit_term(arg.value, f)?;
        }
        Ok(())
    }

    pub fn visit_ctor_def<E, F: Visitor<E>>(
        &self,
        ctor_def_id: CtorDefId,
        f: &mut F,
    ) -> Result<(), E> {
        let ctor_def = ctor_def_id.value();

        // Visit the parameters
        self.visit_params(ctor_def.params, f)?;

        // Create a new type for the result of the constructor, and traverse it.
        let return_ty =
            Ty::from(DataTy { data_def: ctor_def.data_def_id, args: ctor_def.result_args });
        self.visit_ty(return_ty, f)?;

        Ok(())
    }

    pub fn visit_data_def<E, F: Visitor<E>>(
        &self,
        data_def_id: DataDefId,
        f: &mut F,
    ) -> Result<(), E> {
        let (data_def_params, data_def_ctors) =
            data_def_id.map(|data_def| (data_def.params, data_def.ctors));

        // Params
        self.visit_params(data_def_params, f)?;

        match data_def_ctors {
            DataDefCtors::Defined(data_def_ctors_id) => {
                // Traverse the constructors
                for ctor_idx in data_def_ctors_id.to_index_range() {
                    self.visit_ctor_def(CtorDefId(data_def_ctors_id, ctor_idx), f)?;
                }
                Ok(())
            }
            DataDefCtors::Primitive(primitive) => match primitive {
                PrimitiveCtorInfo::Numeric(_)
                | PrimitiveCtorInfo::Str
                | PrimitiveCtorInfo::Char => {
                    // Nothing to do
                    Ok(())
                }
                PrimitiveCtorInfo::Array(list_ctor_info) => {
                    // Traverse the inner type
                    self.visit_ty(list_ctor_info.element_ty, f)?;
                    Ok(())
                }
            },
        }
    }

    pub fn visit_mod_member<E, F: Visitor<E>>(
        &self,
        mod_member_id: ModMemberId,
        f: &mut F,
    ) -> Result<(), E> {
        let value = mod_member_id.borrow().value;
        match value {
            ModMemberValue::Data(data_def_id) => {
                self.visit_data_def(data_def_id, f)?;
                Ok(())
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.visit_mod_def(mod_def_id, f)?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.visit_fn_def(fn_def_id, f)?;
                Ok(())
            }
        }
    }

    pub fn visit_mod_def<E, F: Visitor<E>>(
        &self,
        mod_def_id: ModDefId,
        f: &mut F,
    ) -> Result<(), E> {
        for member in mod_def_id.borrow().members.iter() {
            self.visit_mod_member(member, f)?;
        }
        Ok(())
    }
}
