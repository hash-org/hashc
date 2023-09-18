//! Utilities to traverse the TIR.
use core::fmt;
use std::{cell::RefCell, collections::HashSet, ops::ControlFlow};

use hash_ast::ast::AstNodeId;
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::derive_more::{From, TryInto};

use crate::{
    scopes::{AssignTerm, BlockStatement, BlockStatementsId, BlockTerm, Decl},
    tir::{
        AccessTerm, Arg, ArgsId, ArrayPat, ArrayTerm, CallTerm, CastTerm, CtorDefId, CtorPat,
        CtorTerm, DataDefCtors, DataDefId, DataTy, DerefTerm, FnDef, FnDefId, FnTy, HasAstNodeId,
        IfPat, IndexTerm, LoopTerm, MatchCase, MatchTerm, ModDefId, ModMemberId, ModMemberValue,
        Node, NodeId, NodeOrigin, NodesId, OrPat, Param, ParamsId, Pat, PatArg, PatArgsId, PatId,
        PatListId, PatOrCapture, PrimitiveCtorInfo, RefTerm, RefTy, ReturnTerm, Term, TermId,
        TermListId, TuplePat, TupleTerm, TupleTy, Ty, TyOfTerm, UnsafeTerm,
    },
};

/// An atom in the TIR.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, From, TryInto)]
pub enum Atom {
    Term(TermId),
    FnDef(FnDefId),
    Pat(PatId),
}

impl Atom {
    pub fn origin(self) -> NodeOrigin {
        match self {
            Atom::Term(t) => t.origin(),
            Atom::FnDef(f) => f.origin(),
            Atom::Pat(p) => p.origin(),
        }
    }
}

impl HasAstNodeId for Atom {
    fn node_id(&self) -> Option<AstNodeId> {
        match self {
            Atom::Term(t) => t.node_id(),
            Atom::FnDef(f) => f.node_id(),
            Atom::Pat(p) => p.node_id(),
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Term(term_id) => write!(f, "{}", term_id),
            Atom::FnDef(fn_def_id) => write!(f, "{}", fn_def_id),
            Atom::Pat(pat_id) => write!(f, "{}", pat_id),
        }
    }
}

/// Contains methods to traverse the Hash TIR structure.
pub struct Visitor {
    visited: RefCell<HashSet<Atom>>,
    visit_fns_once: bool,
}

/// Contains the implementation of `fmap` and `visit` for each atom, as well as
/// secondary components such as arguments and parameters.
impl Visitor {
    /// Create a new `TraversingUtils`.
    pub fn new() -> Self {
        Self { visited: RefCell::new(HashSet::new()), visit_fns_once: true }
    }

    pub fn set_visit_fns_once(&mut self, once: bool) {
        self.visit_fns_once = once;
    }
}

impl Default for Visitor {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait to visit a TIR node `X`, by mutating the node.
pub trait Visit<X> {
    /// Visit and mutate TIR node `X` through a function.
    fn try_visit<E, F: TryVisitFn<E>>(&self, x: X, f: &mut F) -> Result<(), E>;

    /// Visit and mutate TIR node `X` through a function (infallible).
    fn visit<F: VisitFn>(&self, x: X, f: &mut F) {
        self.try_visit::<!, _>(x, &mut |a| Ok(f(a))).into_ok()
    }
}

/// Trait to map a TIR node `X` to another node of the same type `X`, without
/// mutating the original.
pub trait Map<X> {
    /// Map a TIR node `X` to another node of the same type `X` through a
    /// function.
    fn map<E, F: MapFn<E>>(&self, x: X, f: F) -> Result<X, E>;

    /// Deep-copy a TIR node `X`.
    fn copy(&self, x: X) -> X {
        self.map::<!, _>(x, |_| Ok(ControlFlow::Continue(()))).into_ok()
    }
}

/// Function to visit an atom.
///
/// This does not return a value, but instead returns a `ControlFlow` to
/// indicate whether to continue or break the traversal.
pub trait TryVisitFn<E> = FnMut(Atom) -> Result<ControlFlow<()>, E>;
pub trait VisitFn = FnMut(Atom) -> ControlFlow<()>;

/// Function to map an atom to another atom.
///
/// This returns a `ControlFlow` to indicate whether to continue by duplicating
/// the atom canonically or break the traversal with a custom atom.
pub trait MapFn<E> = Fn(Atom) -> Result<ControlFlow<Atom>, E> + Copy;

impl Visit<Atom> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, atom: Atom, f: &mut F) -> Result<(), E> {
        match atom {
            Atom::Term(term_id) => self.try_visit(term_id, f),
            Atom::FnDef(fn_def_id) => self.try_visit(fn_def_id, f),
            Atom::Pat(pat_id) => self.try_visit(pat_id, f),
        }
    }
}

impl Map<Atom> for Visitor {
    fn map<E, F: MapFn<E>>(&self, atom: Atom, f: F) -> Result<Atom, E> {
        match atom {
            Atom::Term(term_id) => Ok(Atom::Term(self.map(term_id, f)?)),
            Atom::FnDef(fn_def_id) => Ok(Atom::FnDef(self.map(fn_def_id, f)?)),
            Atom::Pat(pat_id) => Ok(Atom::Pat(self.map(pat_id, f)?)),
        }
    }
}

impl Visit<TermId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, term_id: TermId, f: &mut F) -> Result<(), E> {
        match f(term_id.into())? {
            ControlFlow::Break(_) => Ok(()),
            ControlFlow::Continue(()) => match *term_id.value() {
                Term::Tuple(tuple_term) => self.try_visit(tuple_term.data, f),
                Term::Lit(_) => Ok(()),
                Term::Array(list_ctor) => self.try_visit(list_ctor.elements, f),
                Term::Ctor(ctor_term) => {
                    self.try_visit(ctor_term.data_args, f)?;
                    self.try_visit(ctor_term.ctor_args, f)
                }
                Term::Call(fn_call_term) => {
                    self.try_visit(fn_call_term.subject, f)?;
                    self.try_visit(fn_call_term.args, f)
                }
                Term::Fn(fn_def_id) => self.try_visit(fn_def_id, f),
                Term::Block(block_term) => {
                    self.try_visit(block_term.statements, f)?;
                    self.try_visit(block_term.expr, f)
                }
                Term::Var(_) => Ok(()),
                Term::Loop(loop_term) => self.try_visit(loop_term.inner, f),
                Term::LoopControl(_) => Ok(()),
                Term::Match(match_term) => {
                    self.try_visit(match_term.subject, f)?;
                    for case in match_term.cases.elements().value() {
                        self.try_visit(case.bind_pat, f)?;
                        self.try_visit(case.value, f)?;
                    }
                    Ok(())
                }
                Term::Return(return_term) => self.try_visit(return_term.expression, f),
                Term::Assign(assign_term) => {
                    self.try_visit(assign_term.subject, f)?;
                    self.try_visit(assign_term.value, f)
                }
                Term::Unsafe(unsafe_term) => self.try_visit(unsafe_term.inner, f),
                Term::Access(access_term) => self.try_visit(access_term.subject, f),
                Term::Index(index_term) => {
                    self.try_visit(index_term.subject, f)?;
                    self.try_visit(index_term.index, f)
                }
                Term::Cast(cast_term) => {
                    self.try_visit(cast_term.subject_term, f)?;
                    self.try_visit(cast_term.target_ty, f)
                }
                Term::TypeOf(type_of_term) => self.try_visit(type_of_term.term, f),
                Term::Ref(ref_term) => self.try_visit(ref_term.subject, f),
                Term::Deref(deref_term) => self.try_visit(deref_term.subject, f),
                Term::Hole(_) => Ok(()),
                Term::Intrinsic(_) => Ok(()),
                Ty::TupleTy(tuple_ty) => self.try_visit(tuple_ty.data, f),
                Ty::FnTy(fn_ty) => {
                    self.try_visit(fn_ty.params, f)?;
                    self.try_visit(fn_ty.return_ty, f)
                }
                Ty::RefTy(ref_ty) => self.try_visit(ref_ty.ty, f),
                Ty::DataTy(data_ty) => self.try_visit(data_ty.args, f),
                Ty::Universe => Ok(()),
            },
        }
    }
}

impl Map<TermId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, term_id: TermId, f: F) -> Result<TermId, E> {
        let origin = term_id.origin();
        let result = match f(term_id.into())? {
            ControlFlow::Break(atom) => match atom {
                Atom::Term(t) => Ok(t),
                Atom::FnDef(fn_def_id) => Ok(Node::create_at(Term::Fn(fn_def_id), origin)),
                Atom::Pat(_) => unreachable!("cannot use a pattern as a term"),
            },
            ControlFlow::Continue(()) => match *term_id.value() {
                Term::Tuple(tuple_term) => {
                    let data = self.map(tuple_term.data, f)?;
                    Ok(Term::from(Term::Tuple(TupleTerm { data }), origin))
                }
                Term::Lit(lit) => Ok(Term::from(Term::Lit(lit), origin)),
                Term::Array(list_ctor) => {
                    let elements = self.map(list_ctor.elements, f)?;
                    Ok(Term::from(Term::Array(ArrayTerm { elements }), origin))
                }
                Term::Ctor(ctor_term) => {
                    let data_args = self.map(ctor_term.data_args, f)?;
                    let ctor_args = self.map(ctor_term.ctor_args, f)?;
                    Ok(Term::from(CtorTerm { ctor: ctor_term.ctor, data_args, ctor_args }, origin))
                }
                Term::Call(fn_call_term) => {
                    let subject = self.map(fn_call_term.subject, f)?;
                    let args = self.map(fn_call_term.args, f)?;
                    Ok(Term::from(
                        CallTerm { args, subject, implicit: fn_call_term.implicit },
                        origin,
                    ))
                }
                Term::Fn(fn_def_id) => {
                    let fn_def_id = self.map(fn_def_id, f)?;
                    Ok(Term::from(Term::Fn(fn_def_id), origin))
                }
                Term::Block(block_term) => {
                    let statements = self.map(block_term.statements, f)?;
                    let expr = self.map(block_term.expr, f)?;
                    Ok(Term::from(
                        BlockTerm { statements, stack_id: block_term.stack_id, expr },
                        origin,
                    ))
                }
                Term::Var(var_term) => Ok(Term::from(var_term, origin)),
                Term::Loop(loop_term) => {
                    let inner = self.map(loop_term.inner, f)?;
                    Ok(Term::from(LoopTerm { inner }, origin))
                }
                Term::LoopControl(loop_control_term) => Ok(Term::from(loop_control_term, origin)),
                Term::Match(match_term) => {
                    let subject = self.map(match_term.subject, f)?;

                    let cases = Node::<MatchCase>::seq(
                        match_term
                            .cases
                            .value()
                            .iter()
                            .map(|case| {
                                let case_value = case.value();
                                let bind_pat = self.map(case_value.bind_pat, f)?;
                                let value = self.map(case_value.value, f)?;
                                Ok(Node::at(
                                    MatchCase { bind_pat, value, stack_id: case_value.stack_id },
                                    case_value.origin,
                                ))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    Ok(Term::from(
                        MatchTerm {
                            cases: Node::create_at(cases, match_term.cases.origin()),
                            subject,
                            origin: match_term.origin,
                        },
                        origin,
                    ))
                }
                Term::Return(return_term) => {
                    let expression = self.map(return_term.expression, f)?;
                    Ok(Term::from(ReturnTerm { expression }, origin))
                }
                Term::Assign(assign_term) => {
                    let subject = self.map(assign_term.subject, f)?;
                    let value = self.map(assign_term.value, f)?;
                    Ok(Term::from(AssignTerm { subject, value }, origin))
                }
                Term::Unsafe(unsafe_term) => {
                    let inner = self.map(unsafe_term.inner, f)?;
                    Ok(Term::from(UnsafeTerm { inner }, origin))
                }
                Term::Access(access_term) => {
                    let subject = self.map(access_term.subject, f)?;
                    Ok(Term::from(AccessTerm { subject, field: access_term.field }, origin))
                }
                Term::Index(index_term) => {
                    let subject = self.map(index_term.subject, f)?;
                    let index = self.map(index_term.index, f)?;
                    Ok(Term::from(IndexTerm { subject, index }, origin))
                }
                Term::Cast(cast_term) => {
                    let subject_term = self.map(cast_term.subject_term, f)?;
                    let target_ty = self.map(cast_term.target_ty, f)?;
                    Ok(Term::from(CastTerm { subject_term, target_ty }, origin))
                }
                Term::TypeOf(type_of_term) => {
                    let term = self.map(type_of_term.term, f)?;
                    Ok(Term::from(TyOfTerm { term }, origin))
                }
                Term::Ref(ref_term) => {
                    let subject = self.map(ref_term.subject, f)?;
                    Ok(Term::from(
                        RefTerm { subject, kind: ref_term.kind, mutable: ref_term.mutable },
                        origin,
                    ))
                }
                Term::Deref(deref_term) => {
                    let subject = self.map(deref_term.subject, f)?;
                    Ok(Term::from(DerefTerm { subject }, origin))
                }
                Term::Hole(hole_term) => Ok(Term::from(hole_term, origin)),
                Term::Intrinsic(intrinsic) => Ok(Term::from(intrinsic, origin)),
                Ty::TupleTy(tuple_ty) => {
                    let data = self.map(tuple_ty.data, f)?;
                    Ok(Ty::from(TupleTy { data }, origin))
                }
                Ty::FnTy(fn_ty) => {
                    let params = self.map(fn_ty.params, f)?;
                    let return_ty = self.map(fn_ty.return_ty, f)?;
                    Ok(Ty::from(
                        FnTy {
                            params,
                            return_ty,
                            implicit: fn_ty.implicit,
                            is_unsafe: fn_ty.is_unsafe,
                            pure: fn_ty.pure,
                        },
                        origin,
                    ))
                }
                Ty::RefTy(ref_ty) => {
                    let ty = self.map(ref_ty.ty, f)?;
                    Ok(Ty::from(RefTy { ty, kind: ref_ty.kind, mutable: ref_ty.mutable }, origin))
                }
                Ty::DataTy(data_ty) => {
                    let args = self.map(data_ty.args, f)?;
                    Ok(Ty::from(DataTy { args, data_def: data_ty.data_def }, origin))
                }
                Ty::Universe => Ok(Ty::from(Ty::Universe, origin)),
            },
        }?;

        Ok(result)
    }
}

impl Visit<PatId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, pat_id: PatId, f: &mut F) -> Result<(), E> {
        match f(pat_id.into())? {
            ControlFlow::Break(()) => Ok(()),
            ControlFlow::Continue(()) => match *pat_id.value() {
                Pat::Binding(_) | Pat::Range(_) | Pat::Lit(_) => Ok(()),
                Pat::Tuple(tuple_pat) => self.try_visit(tuple_pat.data, f),
                Pat::Array(list_pat) => self.try_visit(list_pat.pats, f),
                Pat::Ctor(ctor_pat) => {
                    self.try_visit(ctor_pat.data_args, f)?;
                    self.try_visit(ctor_pat.ctor_pat_args, f)
                }
                Pat::Or(or_pat) => self.try_visit(or_pat.alternatives, f),
                Pat::If(if_pat) => {
                    self.try_visit(if_pat.pat, f)?;
                    self.try_visit(if_pat.condition, f)
                }
            },
        }
    }
}
impl Map<PatId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, pat_id: PatId, f: F) -> Result<PatId, E> {
        let origin = pat_id.origin();
        let result = match f(pat_id.into())? {
            ControlFlow::Break(pat) => Ok(PatId::try_from(pat).unwrap()),
            ControlFlow::Continue(()) => match *pat_id.value() {
                Pat::Binding(binding_pat) => Ok(Node::create_at(Pat::from(binding_pat), origin)),
                Pat::Range(range_pat) => Ok(Node::create_at(Pat::from(range_pat), origin)),
                Pat::Lit(lit_pat) => Ok(Node::create_at(Pat::from(lit_pat), origin)),
                Pat::Tuple(tuple_pat) => {
                    let data = self.map(tuple_pat.data, f)?;
                    Ok(Node::create_at(
                        Pat::from(TuplePat { data_spread: tuple_pat.data_spread, data }),
                        origin,
                    ))
                }
                Pat::Array(list_pat) => {
                    let pats = self.map(list_pat.pats, f)?;
                    Ok(Node::create_at(
                        Pat::from(ArrayPat { spread: list_pat.spread, pats }),
                        origin,
                    ))
                }
                Pat::Ctor(ctor_pat) => {
                    let data_args = self.map(ctor_pat.data_args, f)?;
                    let ctor_pat_args = self.map(ctor_pat.ctor_pat_args, f)?;
                    Ok(Node::create_at(
                        Pat::from(CtorPat {
                            data_args,
                            ctor_pat_args,
                            ctor: ctor_pat.ctor,
                            ctor_pat_args_spread: ctor_pat.ctor_pat_args_spread,
                        }),
                        origin,
                    ))
                }
                Pat::Or(or_pat) => {
                    let alternatives = self.map(or_pat.alternatives, f)?;
                    Ok(Node::create_at(Pat::from(OrPat { alternatives }), origin))
                }
                Pat::If(if_pat) => {
                    let pat = self.map(if_pat.pat, f)?;
                    let condition = self.map(if_pat.condition, f)?;
                    Ok(Node::create_at(Pat::from(IfPat { pat, condition }), origin))
                }
            },
        }?;

        Ok(result)
    }
}

impl Visit<BlockStatementsId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(
        &self,
        block_statements: BlockStatementsId,
        f: &mut F,
    ) -> Result<(), E> {
        for statement in block_statements.elements().value() {
            match *statement {
                BlockStatement::Decl(decl) => {
                    self.try_visit(decl.bind_pat, f)?;
                    self.try_visit(decl.ty, f)?;
                    decl.value.map(|v| self.try_visit(v, f)).transpose()?;
                }
                BlockStatement::Expr(expr) => {
                    self.try_visit(expr, f)?;
                }
            }
        }
        Ok(())
    }
}
impl Map<BlockStatementsId> for Visitor {
    fn map<E, F: MapFn<E>>(
        &self,
        block_statements: BlockStatementsId,
        f: F,
    ) -> Result<BlockStatementsId, E> {
        let mut new_list = Vec::with_capacity(block_statements.len());
        for statement in block_statements.elements().value() {
            match *statement {
                BlockStatement::Decl(decl) => {
                    let bind_pat = self.map(decl.bind_pat, f)?;
                    let ty = self.map(decl.ty, f)?;
                    let value = decl.value.map(|v| self.map(v, f)).transpose()?;
                    new_list.push(Node::at(
                        BlockStatement::Decl(Decl { ty, bind_pat, value }),
                        statement.origin,
                    ));
                }
                BlockStatement::Expr(expr) => {
                    new_list
                        .push(Node::at(BlockStatement::Expr(self.map(expr, f)?), statement.origin));
                }
            }
        }
        Ok(Node::create_at(Node::seq(new_list), block_statements.origin()))
    }
}

impl Visit<TermListId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, term_list_id: TermListId, f: &mut F) -> Result<(), E> {
        for term in term_list_id.elements().value() {
            self.try_visit(term, f)?;
        }
        Ok(())
    }
}
impl Map<TermListId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, term_list: TermListId, f: F) -> Result<TermListId, E> {
        let mut new_list = Vec::with_capacity(term_list.len());
        for term_id in term_list.elements().value() {
            new_list.push(self.map(term_id, f)?);
        }
        Ok(Node::create_at(TermId::seq(new_list), term_list.origin()))
    }
}

impl Visit<PatListId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, pat_list_id: PatListId, f: &mut F) -> Result<(), E> {
        for pat in pat_list_id.elements().value() {
            if let PatOrCapture::Pat(pat) = pat {
                self.try_visit(pat, f)?;
            }
        }
        Ok(())
    }
}
impl Map<PatListId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, pat_list: PatListId, f: F) -> Result<PatListId, E> {
        let mut new_list = Vec::with_capacity(pat_list.len());
        for pat_id in pat_list.elements().value() {
            match pat_id {
                PatOrCapture::Pat(pat_id) => {
                    new_list.push(PatOrCapture::Pat(self.map(pat_id, f)?));
                }
                PatOrCapture::Capture(node) => {
                    new_list.push(PatOrCapture::Capture(node));
                }
            }
        }
        Ok(Node::create_at(PatOrCapture::seq(new_list), pat_list.origin()))
    }
}

impl Visit<ParamsId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, params_id: ParamsId, f: &mut F) -> Result<(), E> {
        for param in params_id.elements().value() {
            self.try_visit(param.ty, f)?;
            if let Some(default) = param.default {
                self.try_visit(default, f)?;
            }
        }
        Ok(())
    }
}
impl Map<ParamsId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, params_id: ParamsId, f: F) -> Result<ParamsId, E> {
        let new_params = {
            let mut new_params = Vec::with_capacity(params_id.len());
            for param in params_id.elements().value() {
                new_params.push(Node::at(
                    Param {
                        name: param.name,
                        ty: self.map(param.ty, f)?,
                        default: param.default.map(|default| self.map(default, f)).transpose()?,
                    },
                    param.origin,
                ));
            }
            Ok(Node::create_at(Node::<Param>::seq(new_params), params_id.origin()))
        }?;

        Ok(new_params)
    }
}

impl Visit<ArgsId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, args_id: ArgsId, f: &mut F) -> Result<(), E> {
        for arg in args_id.elements().value() {
            self.try_visit(arg.value, f)?;
        }
        Ok(())
    }
}
impl Map<ArgsId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, args_id: ArgsId, f: F) -> Result<ArgsId, E> {
        let mut new_args = Vec::with_capacity(args_id.len());
        for arg in args_id.elements().value() {
            new_args.push(Node::at(
                Arg { target: arg.target, value: self.map(arg.value, f)? },
                arg.origin,
            ));
        }
        let new_args_id = Node::create_at(Node::<Arg>::seq(new_args), args_id.origin());
        Ok(new_args_id)
    }
}

impl Visit<PatArgsId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, pat_args_id: PatArgsId, f: &mut F) -> Result<(), E> {
        for arg in pat_args_id.elements().value() {
            if let PatOrCapture::Pat(pat) = arg.pat {
                self.try_visit(pat, f)?;
            }
        }
        Ok(())
    }
}
impl Map<PatArgsId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, pat_args_id: PatArgsId, f: F) -> Result<PatArgsId, E> {
        let new_pat_args = {
            let mut new_args = Vec::with_capacity(pat_args_id.len());
            for pat_arg in pat_args_id.elements().value() {
                new_args.push(Node::at(
                    PatArg {
                        target: pat_arg.target,
                        pat: match pat_arg.pat {
                            PatOrCapture::Pat(pat_id) => PatOrCapture::Pat(self.map(pat_id, f)?),
                            PatOrCapture::Capture(node) => PatOrCapture::Capture(node),
                        },
                    },
                    pat_arg.origin,
                ));
            }
            Ok(Node::create_at(Node::<PatArg>::seq(new_args), pat_args_id.origin()))
        }?;

        Ok(new_pat_args)
    }
}

impl Visit<FnDefId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, fn_def_id: FnDefId, f: &mut F) -> Result<(), E> {
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
                self.try_visit(fn_ty.params, f)?;
                self.try_visit(fn_ty.return_ty, f)?;
                self.try_visit(fn_def.body, f)
            }
        }
    }
}
impl Map<FnDefId> for Visitor {
    fn map<E, F: MapFn<E>>(&self, fn_def_id: FnDefId, f: F) -> Result<FnDefId, E> {
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
                let params = self.map(fn_def.ty.params, f)?;
                let return_ty = self.map(fn_def.ty.return_ty, f)?;
                let body = self.map(fn_def.body, f)?;

                let def = Node::create_at(
                    FnDef {
                        name: fn_def.name,
                        ty: FnTy {
                            params,
                            return_ty,
                            implicit: fn_def.ty.implicit,
                            is_unsafe: fn_def.ty.is_unsafe,
                            pure: fn_def.ty.pure,
                        },
                        body,
                    },
                    fn_def.origin,
                );

                Ok(def)
            }
        }?;

        Ok(new_fn_def)
    }
}

impl Visit<CtorDefId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, ctor_def_id: CtorDefId, f: &mut F) -> Result<(), E> {
        let ctor_def = ctor_def_id.value();

        // Visit the parameters
        self.try_visit(ctor_def.params, f)?;

        // Visit the arguments
        self.try_visit(ctor_def.result_args, f)?;

        Ok(())
    }
}

impl Visit<DataDefId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, data_def_id: DataDefId, f: &mut F) -> Result<(), E> {
        let (data_def_params, data_def_ctors) =
            data_def_id.map(|data_def| (data_def.params, data_def.ctors));

        // Params
        self.try_visit(data_def_params, f)?;

        match data_def_ctors {
            DataDefCtors::Defined(data_def_ctors_id) => {
                // Traverse the constructors
                for ctor_idx in data_def_ctors_id.value().to_index_range() {
                    self.try_visit(CtorDefId(data_def_ctors_id.elements(), ctor_idx), f)?;
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
                    self.try_visit(list_ctor_info.element_ty, f)?;
                    Ok(())
                }
            },
        }
    }
}

impl Visit<ModMemberId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(
        &self,
        mod_member_id: ModMemberId,
        f: &mut F,
    ) -> Result<(), E> {
        let value = mod_member_id.borrow().value;
        match value {
            ModMemberValue::Data(data_def_id) => {
                self.try_visit(data_def_id, f)?;
                Ok(())
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.try_visit(mod_def_id, f)?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.try_visit(fn_def_id, f)?;
                Ok(())
            }
            ModMemberValue::Intrinsic(_) => {
                // Nothing to do
                Ok(())
            }
        }
    }
}

impl Visit<ModDefId> for Visitor {
    fn try_visit<E, F: TryVisitFn<E>>(&self, mod_def_id: ModDefId, f: &mut F) -> Result<(), E> {
        for member in mod_def_id.borrow().members.iter() {
            self.try_visit(member, f)?;
        }
        Ok(())
    }
}
