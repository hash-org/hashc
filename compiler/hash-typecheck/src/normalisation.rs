//! Operations for normalising terms and types.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref, From};
use hash_ast::ast::RangeEnd;
use hash_tir::new::{
    access::AccessTerm,
    args::{ArgData, ArgsId, PatArgsId},
    casting::CastTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    environment::context::{BindingKind, ScopeKind},
    fns::{FnBody, FnCallTerm},
    lits::{ListCtor, Lit, LitPat, PrimTerm},
    pats::{Pat, PatId, Spread},
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclTerm, StackMemberId},
    symbols::Symbol,
    terms::{Term, TermId, UnsafeTerm},
    tuples::TupleTerm,
    tys::{Ty, TyId, TypeOfTerm},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{PartialStore, SequenceStore, SequenceStoreKey, Store};
use itertools::Itertools;

use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

#[derive(Constructor, Deref)]
pub struct NormalisationOps<'a, T: AccessToTypechecking>(&'a T);

/// Represents a normalisation result.
#[derive(Debug, Clone, From)]
pub enum Signal {
    Break,
    Continue,
    Return(Atom),
    Err(TcError),
}

/// The result of matching a pattern against a term.
enum MatchResult {
    /// The pattern matched successfully.
    Successful,
    /// The pattern failed to match.
    Failed,
    /// The term could not be normalised enough to be matched.
    Stuck,
}

impl<T: AccessToTypechecking> NormalisationOps<'_, T> {
    /// Normalise the given atom.
    pub fn normalise(&self, atom: Atom) -> TcResult<Atom> {
        match self.eval(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                Signal::Break | Signal::Continue | Signal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                Signal::Err(e) => Err(e),
            },
        }
    }

    /// Normalise the given atom, and try to use it as a type.
    pub fn normalise_to_ty(&self, atom: Atom) -> TcResult<Option<TyId>> {
        match self.normalise(atom)? {
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Ok(Some(ty)),
                Term::Var(var) => Ok(Some(self.new_ty(var))),
                _ => Ok(None),
            },
            Atom::Ty(ty) => Ok(Some(ty)),
            _ => Ok(None),
        }
    }

    /// Evaluate an atom.
    fn eval(&self, atom: Atom) -> Result<Atom, Signal> {
        self.traversing_utils().fmap_atom(atom, |atom| self.eval_once(atom))
    }

    /// Evaluate a block term.
    fn eval_block(&self, block_term: BlockTerm) -> Result<Atom, Signal> {
        self.context().enter_scope(ScopeKind::Stack(block_term.stack_id), || {
            for statement in block_term
                .statements
                .to_index_range()
                .map(|i| self.stores().term_list().get_at_index(block_term.statements, i))
            {
                let _ = self.eval(statement.into())?;
            }
            self.eval(block_term.return_value.into())
        })
    }

    /// Evaluate a variable.
    fn eval_var(&self, var: Symbol) -> Result<Atom, Signal> {
        match self.context().get_binding(var).unwrap().kind {
            BindingKind::Param(_, _) => Ok(self.new_term(var).into()),
            BindingKind::Arg(_, arg_id) => {
                Ok(self.stores().args().map_fast(arg_id.0, |args| args[arg_id.1].value).into())
            }
            BindingKind::StackMember(stack_member) => {
                self.stores().stack().map_fast(stack_member.0, |stack| {
                    match stack.members[stack_member.1].value {
                        Some(value) => Ok(value.into()),
                        None => {
                            // @@Todo: make this a user error
                            panic!("Tried to read uninitialised stack member")
                        }
                    }
                })
            }

            // Variables are never bound to a module member, constructor or equality.
            // @@Todo: make types better
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) | BindingKind::Equality(_) => {
                unreachable!()
            }
        }
    }

    /// Evaluate a cast term.
    fn eval_cast(&self, _cast_term: CastTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a reference term.
    fn eval_ref(&self, _ref_term: RefTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a dereference term.
    fn eval_deref(&self, deref_term: DerefTerm) -> Result<ControlFlow<Atom>, Signal> {
        let evaluated_inner = self.eval(deref_term.subject.into())?;
        // Reduce:
        if let Atom::Term(term) = evaluated_inner {
            if let Term::Ref(ref_expr) = self.get_term(term) {
                return Ok(ControlFlow::Break(ref_expr.subject.into()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }

    /// Evaluate an access term.
    fn eval_access(&self, _access_term: AccessTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Evaluate an unsafe term.
    fn eval_unsafe(&self, unsafe_term: UnsafeTerm) -> Result<Atom, Signal> {
        // @@Todo: handle unsafe safety
        self.eval(unsafe_term.inner.into())
    }

    /// Evaluate a `typeof` term.
    fn eval_type_of(&self, type_of_term: TypeOfTerm) -> Result<Atom, Signal> {
        // Infer the type of the term:
        let (_, ty) = self.inference_ops().infer_term(type_of_term.term, None)?;
        Ok(ty.into())
    }

    /// Evaluate a loop control term.
    fn eval_loop_control(&self, loop_control_term: LoopControlTerm) -> Signal {
        match loop_control_term {
            LoopControlTerm::Break => Signal::Break,
            LoopControlTerm::Continue => Signal::Continue,
        }
    }

    /// Evaluate an assignment term.
    fn eval_assign(&self, _assign_term: AssignTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Check if the given atom is the `true` constructor.
    ///
    /// Assumes that the atom is normalised.
    fn is_true(&self, _atom: Atom) -> bool {
        todo!()
    }

    /// Evaluate a match term.
    fn eval_match(&self, _match_term: MatchTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a declaration term.
    fn eval_decl(&self, _decl_term: DeclTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Evaluate a `return` term.
    fn eval_return(&self, return_term: ReturnTerm) -> Result<!, Signal> {
        let normalised = self.eval(return_term.expression.into())?;
        Err(Signal::Return(normalised))
    }

    /// Evaluate a `loop` term.
    fn eval_loop(&self, loop_term: LoopTerm) -> Result<Atom, Signal> {
        loop {
            match self.eval_block(loop_term.block) {
                Ok(_) | Err(Signal::Continue) => continue,
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        Ok(self.new_void_term().into())
    }

    /// Evaluate a term and use it as a type.
    fn eval_ty_eval(&self, term: TermId) -> Result<Atom, Signal> {
        let evaluated = self.eval(term.into())?;
        match evaluated {
            Atom::Ty(_) => Ok(evaluated),
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Ok(ty.into()),
                _ => Ok(evaluated),
            },
            Atom::FnDef(_) | Atom::Pat(_) => unreachable!(),
        }
    }

    /// Evaluate a function call.
    fn eval_fn_call(&self, mut fn_call: FnCallTerm) -> Result<Atom, Signal> {
        let evaluated_inner = self.eval(fn_call.subject.into())?;

        // Beta-reduce:
        if let Atom::Term(term) = evaluated_inner {
            fn_call.subject = term;

            if let Term::FnRef(fn_def_id) = self.get_term(term) {
                let fn_def = self.get_fn_def(fn_def_id);
                // @@Todo: handle pure/impure

                match fn_def.body {
                    FnBody::Defined(defined_fn_def) => {
                        // Make a substitution from the arguments to the parameters:
                        let sub = self.substitution_ops().create_sub_from_applying_args_to_params(
                            fn_call.args,
                            fn_def.ty.params,
                        );

                        // Apply substitution to body:
                        let result =
                            self.substitution_ops().apply_sub_to_term(defined_fn_def, &sub);

                        // Evaluate result:
                        return match self.eval(result.into()) {
                            Err(Signal::Return(result)) | Ok(result) => Ok(result),
                            Err(e) => Err(e),
                        };
                    }

                    FnBody::Intrinsic(intrinsic_id) => {
                        let args_as_terms: Vec<TermId> =
                            self.stores().args().map_fast(fn_call.args, |args| {
                                args.iter().map(|arg| arg.value).collect()
                            });

                        // Run intrinsic:
                        let result: TermId =
                            self.intrinsics().by_id().map_fast(intrinsic_id, |intrinsic| {
                                let intrinsic = intrinsic.unwrap();
                                (intrinsic.implementation)(self.0, &args_as_terms)
                            });

                        return Ok(result.into());
                    }

                    FnBody::Axiom => {
                        // Nothing further to do
                    }
                }
            }
        }

        Ok(self.new_term(fn_call).into())
    }

    /// Evaluate an atom once, for use with `fmap`.
    fn eval_once(&self, atom: Atom) -> Result<ControlFlow<Atom>, Signal> {
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                // Types
                Term::Ty(_) => Ok(ControlFlow::Continue(())),

                // Introduction forms:
                Term::Ref(_)
                | Term::Tuple(_)
                | Term::Hole(_)
                | Term::FnRef(_)
                | Term::Ctor(_)
                | Term::Prim(_) => Ok(ControlFlow::Continue(())),

                // Potentially reducible forms:
                Term::TypeOf(term) => Ok(ControlFlow::Break(self.eval_type_of(term)?)),
                Term::Unsafe(unsafe_expr) => Ok(ControlFlow::Break(self.eval_unsafe(unsafe_expr)?)),
                Term::Match(match_term) => Ok(ControlFlow::Break(self.eval_match(match_term)?)),
                Term::FnCall(fn_call) => Ok(ControlFlow::Break(self.eval_fn_call(fn_call)?)),
                Term::Cast(cast_term) => Ok(ControlFlow::Break(self.eval_cast(cast_term)?)),
                Term::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
                Term::Deref(deref_term) => self.eval_deref(deref_term),
                Term::Access(access_term) => self.eval_access(access_term),

                // Imperative:
                Term::LoopControl(loop_control) => Err(self.eval_loop_control(loop_control)),
                Term::Assign(assign_term) => self.eval_assign(assign_term),
                Term::Decl(decl_term) => self.eval_decl(decl_term),
                Term::Return(return_expr) => self.eval_return(return_expr)?,
                Term::Block(block_term) => Ok(ControlFlow::Break(self.eval_block(block_term)?)),
                Term::Loop(loop_term) => Ok(ControlFlow::Break(self.eval_loop(loop_term)?)),
            },
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Eval(term) => Ok(ControlFlow::Break(self.eval_ty_eval(term)?)),
                Ty::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
                Ty::Data(_)
                | Ty::Universe(_)
                | Ty::Ref(_)
                | Ty::Hole(_)
                | Ty::Tuple(_)
                | Ty::Fn(_) => Ok(ControlFlow::Continue(())),
            },
            Atom::FnDef(_) => Ok(ControlFlow::Break(atom)),
            Atom::Pat(_) => Ok(ControlFlow::Continue(())),
        }
    }

    /// Get a slice of `t` that corresponds to the given spread.
    fn get_spread_slice<'a, M>(
        &self,
        term_list_len: usize,
        pat_list_len: usize,
        spread: Spread,
        t: &'a [M],
    ) -> &'a [M] {
        let spread_end = term_list_len - pat_list_len + spread.index;
        &t[spread.index..spread_end]
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_args(
        &self,
        term_args: ArgsId,
        pat_args: PatArgsId,
        spread: Spread,
    ) -> ArgsId {
        // Create a new tuple term with the spread elements
        let spread_term_args = self.stores().args().map_fast(term_args, |data| {
            self.get_spread_slice(term_args.len(), pat_args.len(), spread, data)
                .iter()
                .map(|data| ArgData { target: data.target, value: data.value })
                .collect_vec()
        });

        self.param_utils().create_args(spread_term_args.into_iter())
    }

    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    fn match_some_list_and_get_binds<TL: SequenceStoreKey, PL: SequenceStoreKey>(
        &self,
        term_list: TL,
        _pat_list: PL,
        spread: Option<Spread>,
        extract_spread_list: impl Fn(Spread) -> (TermId, usize),
        get_ith_pat: impl Fn(usize) -> PatId,
        get_ith_term: impl Fn(usize) -> TermId,
        f: &mut impl FnMut(StackMemberId, TermId),
    ) -> Result<MatchResult, Signal> {
        // We assume that the term list is well-typed with respect to the pattern list.

        let mut element_i = 0;
        while element_i < term_list.len() {
            // Handle spread
            if let Some(spread) = spread && spread.index == element_i {
                let (spread_list, spread_list_len) = extract_spread_list(spread);
                if let Some(member) = spread.stack_member {
                    f(member, spread_list);
                }
                element_i += spread_list_len;
            }

            let arg_i = get_ith_term(element_i);
            let pat_arg_i = get_ith_pat(element_i);

            match self.match_value_and_get_binds(arg_i, pat_arg_i, f)? {
                MatchResult::Successful => {
                    // Continue
                }
                MatchResult::Failed => {
                    // The match failed
                    return Ok(MatchResult::Failed);
                }
                MatchResult::Stuck => {
                    // The match is stuck
                    return Ok(MatchResult::Stuck);
                }
            }

            element_i += 1;
        }

        Ok(MatchResult::Successful)
    }

    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    fn match_args_and_get_binds(
        &self,
        term_args: ArgsId,
        pat_args: PatArgsId,
        spread: Option<Spread>,
        f: &mut impl FnMut(StackMemberId, TermId),
    ) -> Result<MatchResult, Signal> {
        self.match_some_list_and_get_binds(
            term_args,
            pat_args,
            spread,
            |spread| {
                let spread_args = self.extract_spread_args(term_args, pat_args, spread);
                let tuple_term = self.new_term(TupleTerm { data: spread_args });
                (tuple_term, spread_args.len())
            },
            |i| self.stores().pat_args().get_at_index(pat_args, i).pat,
            |i| self.stores().args().get_at_index(term_args, i).value,
            f,
        )
    }

    /// Match a literal with another.
    fn match_literal_to_literal<U: PartialEq>(&self, value: U, pat: U) -> MatchResult {
        if value == pat {
            MatchResult::Successful
        } else {
            MatchResult::Failed
        }
    }

    /// Match a literal between two endpoints.
    fn match_literal_to_range<U: PartialOrd>(
        &self,
        value: U,
        start: U,
        end: U,
        range_end: RangeEnd,
    ) -> MatchResult {
        if range_end == RangeEnd::Included {
            if start <= value && value <= end {
                MatchResult::Successful
            } else {
                MatchResult::Failed
            }
        } else if start <= value && value < end {
            MatchResult::Successful
        } else {
            MatchResult::Failed
        }
    }

    /// Match the given value with the given pattern, running `f` every time a
    /// bind is discovered.
    ///
    /// The term must be normalised and well-typed with respect to the pattern.
    fn match_value_and_get_binds(
        &self,
        term_id: TermId,
        pat_id: PatId,
        f: &mut impl FnMut(StackMemberId, TermId),
    ) -> Result<MatchResult, Signal> {
        match (self.get_term(term_id), self.get_pat(pat_id)) {
            (_, Pat::Or(pats)) => {
                // Try each alternative in turn:
                for pat in pats.alternatives.iter() {
                    let pat = self.stores().pat_list().get_element(pat);
                    // First collect the bindings locally

                    match self.match_value_and_get_binds(term_id, pat, f)? {
                        MatchResult::Successful => {
                            return Ok(MatchResult::Successful);
                        }
                        MatchResult::Failed => {
                            // Try the next alternative
                            continue;
                        }
                        MatchResult::Stuck => {
                            return Ok(MatchResult::Stuck);
                        }
                    }
                }
                Ok(MatchResult::Failed)
            }

            (_, Pat::If(if_pat)) => {
                if let MatchResult::Successful =
                    self.match_value_and_get_binds(term_id, if_pat.pat, f)?
                {
                    // Check the condition:
                    let cond = self.eval(if_pat.condition.into())?;
                    if self.is_true(cond) {
                        return Ok(MatchResult::Successful);
                    }
                }

                Ok(MatchResult::Failed)
            }

            // Bindings, always successful
            (_, Pat::Binding(binding)) => match binding.stack_member {
                Some(member) => {
                    f(member, term_id);
                    Ok(MatchResult::Successful)
                }
                None => Ok(MatchResult::Successful),
            },

            // Tuples
            (Term::Tuple(tuple_term), Pat::Tuple(tuple_pat)) => self.match_args_and_get_binds(
                tuple_term.data,
                tuple_pat.data,
                // Tuples can have spreads, which return tuples
                tuple_pat.data_spread,
                f,
            ),
            (_, Pat::Tuple(_)) => Ok(MatchResult::Stuck),

            // Constructors
            (Term::Ctor(ctor_term), Pat::Ctor(ctor_pat)) => {
                // We assume that the constructor is well-typed with respect to
                // the pattern, so that data params already match.

                if ctor_term.ctor != ctor_pat.ctor {
                    Ok(MatchResult::Failed)
                } else {
                    self.match_args_and_get_binds(
                        ctor_term.ctor_args,
                        ctor_pat.ctor_pat_args,
                        // Constructors can have spreads, which return tuples
                        ctor_pat.ctor_pat_args_spread,
                        f,
                    )
                }
            }
            (_, Pat::Ctor(_)) => Ok(MatchResult::Stuck),

            // Ranges
            (Term::Prim(prim_term), Pat::Range(range_pat)) => match prim_term {
                PrimTerm::Lit(lit_term) => match (lit_term, range_pat.start, range_pat.end) {
                    (Lit::Int(value), LitPat::Int(start), LitPat::Int(end)) => Ok(self
                        .match_literal_to_range(
                            value.value(),
                            start.value(),
                            end.value(),
                            range_pat.range_end,
                        )),
                    (Lit::Str(value), LitPat::Str(start), LitPat::Str(end)) => Ok(self
                        .match_literal_to_range(
                            value.value(),
                            start.value(),
                            end.value(),
                            range_pat.range_end,
                        )),
                    (Lit::Char(value), LitPat::Char(start), LitPat::Char(end)) => Ok(self
                        .match_literal_to_range(
                            value.value(),
                            start.value(),
                            end.value(),
                            range_pat.range_end,
                        )),
                    _ => Ok(MatchResult::Stuck),
                },
                PrimTerm::List(_) => Ok(MatchResult::Stuck),
            },
            (_, Pat::Range(_)) => Ok(MatchResult::Stuck),

            // Literals
            (Term::Prim(prim_term), Pat::Lit(lit_pat)) => match prim_term {
                PrimTerm::Lit(lit_term) => match (lit_term, lit_pat) {
                    (Lit::Int(a), LitPat::Int(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    (Lit::Str(a), LitPat::Str(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    (Lit::Char(a), LitPat::Char(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    _ => Ok(MatchResult::Stuck),
                },
                PrimTerm::List(_) => Ok(MatchResult::Stuck),
            },
            // Lists
            (Term::Prim(prim_term), Pat::List(list_pat)) => match prim_term {
                PrimTerm::List(list_term) => self.match_some_list_and_get_binds(
                    list_term.elements,
                    list_pat.pats,
                    list_pat.spread,
                    |spread| {
                        // Lists can have spreads, which return sublists
                        let spread_list_elements = self.map_term_list(list_term.elements, |list| {
                            self.get_spread_slice(
                                list_term.elements.len(),
                                list_pat.pats.len(),
                                spread,
                                list,
                            )
                            .to_vec()
                        });
                        let spread_list_len = spread_list_elements.len();
                        let spread_list = self.new_term(PrimTerm::List(ListCtor {
                            elements: self.new_term_list(spread_list_elements),
                        }));
                        (spread_list, spread_list_len)
                    },
                    |i| self.stores().pat_list().get_at_index(list_pat.pats, i),
                    |i| self.stores().term_list().get_at_index(list_term.elements, i),
                    f,
                ),
                PrimTerm::Lit(_) => Ok(MatchResult::Stuck),
            },
            (_, Pat::Lit(_)) => Ok(MatchResult::Stuck),
            (_, Pat::List(_)) => Ok(MatchResult::Stuck),
        }
    }
}
