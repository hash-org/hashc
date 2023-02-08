//! Operations for normalising terms and types.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref, From};
use hash_ast::ast::RangeEnd;
use hash_intrinsics::utils::PrimitiveUtils;
use hash_tir::new::{
    access::AccessTerm,
    args::{ArgData, ArgsId, PatArgsId, PatOrCapture},
    casting::CastTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    environment::context::{Binding, BindingKind, ScopeKind},
    fns::{FnBody, FnCallTerm},
    lits::{ListCtor, Lit, LitPat, PrimTerm},
    params::ParamIndex,
    pats::{Pat, PatId, PatListId, Spread},
    refs::DerefTerm,
    scopes::{AssignTerm, BlockTerm, DeclTerm, StackMemberId},
    symbols::Symbol,
    terms::{Term, TermId, TermListId, UnsafeTerm},
    tuples::TupleTerm,
    tys::{Ty, TyId, TypeOfTerm},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::{
    itertools::Itertools,
    store::{PartialStore, SequenceStore, SequenceStoreKey, Store},
};

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

    /// Try to use the given atom as a type.
    pub fn maybe_to_ty(&self, atom: Atom) -> Option<TyId> {
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Some(ty),
                Term::Var(var) => Some(self.new_ty(var)),
                _ => None,
            },
            Atom::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    /// Try to use the given atom as a type.
    pub fn to_ty(&self, atom: Atom) -> TyId {
        self.maybe_to_ty(atom)
            .unwrap_or_else(|| panic!("Cannot convert {} to a type", self.env().with(atom)))
    }

    /// Normalise the given atom, and try to use it as a term.
    pub fn to_term(&self, atom: Atom) -> TermId {
        match atom {
            Atom::Term(term) => term,
            Atom::Ty(ty) => self.new_term(ty),
            Atom::FnDef(fn_def_id) => self.new_term(fn_def_id),
            _ => panic!("Cannot convert {} to a term", self.env().with(atom)),
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

            let sub = self.substitution_ops().create_sub_from_current_stack_members();
            let result_term = self.eval(block_term.return_value.into())?;
            let subbed_result_term = self.substitution_ops().apply_sub_to_atom(result_term, &sub);
            Ok(subbed_result_term)
        })
    }

    /// Evaluate a variable.
    fn eval_var(&self, var: Symbol) -> Result<Atom, Signal> {
        match self.context().get_binding(var).kind {
            BindingKind::Param(_, _) => Ok(self.new_term(var).into()),
            BindingKind::Arg(_, arg_id) => {
                Ok(self.stores().args().map_fast(arg_id.0, |args| args[arg_id.1].value).into())
            }
            BindingKind::StackMember(_, value) => {
                match value {
                    Some(value) => Ok(value.into()),
                    None => {
                        // @@Todo: make this a user error
                        panic!("Tried to read uninitialised stack member")
                    }
                }
            }

            // Variables are never bound to a module member, constructor or equality.
            // @@Todo: make types better
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) | BindingKind::Equality(_) => {
                unreachable!()
            }
        }
    }

    /// Evaluate a cast term.
    fn eval_cast(&self, cast_term: CastTerm) -> Result<Atom, Signal> {
        // @@Todo: will not play well with typeof?; no-op for now
        self.eval(cast_term.subject_term.into())
    }

    /// Evaluate a dereference term.
    fn eval_deref(&self, mut deref_term: DerefTerm) -> Result<ControlFlow<Atom>, Signal> {
        deref_term.subject = self.to_term(self.eval(deref_term.subject.into())?);

        // Reduce:
        if let Term::Ref(ref_expr) = self.get_term(deref_term.subject) {
            return Ok(ControlFlow::Break(ref_expr.subject.into()));
        }

        Ok(ControlFlow::Break(self.new_term(deref_term).into()))
    }

    /// Get the parameter at the given index in the given argument list.
    fn get_param_in_args(&self, args: ArgsId, target: ParamIndex) -> Atom {
        for arg_i in args.iter() {
            let arg = self.stores().args().get_element(arg_i);
            if arg.target == target {
                return arg.value.into();
            }
        }
        panic!("Out of bounds index for access: {}", self.env().with(target))
    }

    /// Set the parameter at the given index in the given argument list.
    fn set_param_in_args(&self, args: ArgsId, target: ParamIndex, value: Atom) {
        let value = self.to_term(value);
        for arg_i in args.iter() {
            let arg = self.stores().args().get_element(arg_i);
            if arg.target == target {
                self.stores().args().modify_fast(arg_i.0, |mut args| args[arg_i.1].value = value);
                return;
            }
        }
        panic!("Out of bounds index for access: {}", self.env().with(target))
    }

    /// Get the term at the given index in the given term list.
    fn get_index_in_list(&self, list: TermListId, target: ParamIndex) -> Atom {
        match target {
            ParamIndex::Name(_) => {
                panic!("Trying to index a list with a name")
            }
            ParamIndex::Position(pos) => {
                self.stores().term_list().map_fast(list, |list| list[pos].into())
            }
        }
    }

    /// Set the term at the given index in the given term list.
    fn set_index_in_list(&self, list: TermListId, target: ParamIndex, value: Atom) {
        match target {
            ParamIndex::Name(_) => {
                panic!("Trying to index a list with a name")
            }
            ParamIndex::Position(pos) => {
                let value = self.to_term(value);
                self.stores().term_list().modify_fast(list, |list| list[pos] = value);
            }
        }
    }

    /// Evaluate an access term.
    fn eval_access(&self, mut access_term: AccessTerm) -> Result<Atom, Signal> {
        access_term.subject = self.to_term(self.eval(access_term.subject.into())?);

        match self.get_term(access_term.subject) {
            Term::Tuple(tuple) => return Ok(self.get_param_in_args(tuple.data, access_term.field)),
            Term::Ctor(ctor) => {
                return Ok(self.get_param_in_args(ctor.ctor_args, access_term.field))
            }
            Term::Prim(prim) => match prim {
                PrimTerm::List(list) => {
                    return Ok(self.get_index_in_list(list.elements, access_term.field))
                }
                PrimTerm::Lit(_) => {}
            },
            _ => {}
        }

        // Couldn't reduce
        Ok(self.new_term(access_term).into())
    }

    /// Evaluate an unsafe term.
    fn eval_unsafe(&self, unsafe_term: UnsafeTerm) -> Result<Atom, Signal> {
        // @@Todo: handle unsafe safety
        self.eval(unsafe_term.inner.into())
    }

    /// Evaluate a `typeof` term.
    fn eval_type_of(&self, type_of_term: TypeOfTerm) -> Result<Atom, Signal> {
        // Infer the type of the term:
        // @@Todo: use stored IDs only? Do not reduce if un-inferrable?
        let (_, ty) = self.inference_ops().infer_term(type_of_term.term, self.new_ty_hole())?;
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
    fn eval_assign(&self, mut assign_term: AssignTerm) -> Result<Atom, Signal> {
        assign_term.value = self.to_term(self.eval(assign_term.value.into())?);

        match assign_term.index {
            Some(field) => {
                assign_term.subject = self.to_term(self.eval(assign_term.subject.into())?);
                match self.get_term(assign_term.subject) {
                    Term::Tuple(tuple) => {
                        self.set_param_in_args(tuple.data, field, assign_term.value.into())
                    }
                    Term::Ctor(ctor) => {
                        self.set_param_in_args(ctor.ctor_args, field, assign_term.value.into())
                    }
                    Term::Prim(PrimTerm::List(list)) => {
                        self.set_index_in_list(list.elements, field, assign_term.value.into())
                    }
                    _ => panic!("Invalid access"),
                }
            }
            None => match self.get_term(assign_term.subject) {
                // @@Todo: deref
                Term::Var(var) => {
                    let (member, _) = self.context_utils().get_stack_binding(var);
                    self.set_stack_member(member, assign_term.value);
                }
                _ => panic!("Invalid assign {}", self.env().with(&assign_term)),
            },
        }

        Ok(self.new_void_term().into())
    }

    /// Push the given stack member to the stack with no value.
    fn push_stack_uninit(&self, stack_member_id: StackMemberId) {
        self.context().add_binding(Binding {
            name: self.get_stack_member_name(stack_member_id),
            kind: BindingKind::StackMember(stack_member_id, None),
        })
    }

    /// Push the given stack member to the stack with the given value.
    fn push_stack(&self, stack_member_id: StackMemberId, value: TermId) {
        self.context().add_binding(Binding {
            name: self.get_stack_member_name(stack_member_id),
            kind: BindingKind::StackMember(stack_member_id, Some(value)),
        })
    }

    /// Set the given stack member to the given value.
    fn set_stack_member(&self, stack_member_id: StackMemberId, value: TermId) {
        let name = self
            .stores()
            .stack()
            .modify_fast(stack_member_id.0, |stack| stack.members[stack_member_id.1].name);
        self.context().modify_binding(Binding {
            name,
            kind: BindingKind::StackMember(stack_member_id, value.into()),
        })
    }

    /// Evaluate a match term.
    fn eval_match(&self, mut match_term: MatchTerm) -> Result<ControlFlow<Atom>, Signal> {
        match_term.subject = self.to_term(self.eval(match_term.subject.into())?);

        for case_id in match_term.cases.iter() {
            let case = self.stores().match_cases().get_element(case_id);
            let mut outcome = None;

            self.context().enter_scope(case.stack_id.into(), || -> Result<(), Signal> {
                match self.match_value_and_get_binds(
                    match_term.subject,
                    case.bind_pat,
                    &mut |stack_member_id, term_id| self.push_stack(stack_member_id, term_id),
                )? {
                    MatchResult::Successful => {
                        outcome = Some(Ok(ControlFlow::Break(self.eval(case.value.into())?)));
                    }
                    MatchResult::Failed => {}
                    MatchResult::Stuck => {
                        outcome = Some(Ok(ControlFlow::Break(self.new_term(match_term).into())));
                    }
                }

                Ok(())
            })?;

            match outcome {
                Some(outcome) => return outcome,
                None => continue,
            }
        }

        panic!("Non-exhaustive match: {}", self.env().with(&match_term))
    }

    /// Evaluate a declaration term.
    fn eval_decl(&self, mut decl_term: DeclTerm) -> Result<ControlFlow<Atom>, Signal> {
        let current_stack_id = self.context_utils().get_current_stack();
        decl_term.value = decl_term
            .value
            .map(|v| -> Result<_, Signal> { Ok(self.to_term(self.eval(v.into())?)) })
            .transpose()?;

        match decl_term.value {
            Some(value) => match self.match_value_and_get_binds(
                value,
                decl_term.bind_pat,
                &mut |stack_member_id, term_id| self.push_stack(stack_member_id, term_id),
            )? {
                MatchResult::Successful => {
                    // All good
                    Ok(ControlFlow::Break(self.new_void_term().into()))
                }
                MatchResult::Failed => {
                    panic!("Non-exhaustive let-binding: {}", self.env().with(&decl_term))
                }
                MatchResult::Stuck => Ok(ControlFlow::Break(self.new_term(decl_term).into())),
            },
            None => {
                for i in decl_term.iter_stack_indices() {
                    self.push_stack_uninit((current_stack_id, i))
                }
                Ok(ControlFlow::Break(self.new_void_term().into()))
            }
        }
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
                        let sub = self
                            .substitution_ops()
                            .create_sub_from_args_of_params(fn_call.args, fn_def.ty.params);

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
                Term::Match(match_term) => self.eval_match(match_term),
                Term::FnCall(fn_call) => Ok(ControlFlow::Break(self.eval_fn_call(fn_call)?)),
                Term::Cast(cast_term) => Ok(ControlFlow::Break(self.eval_cast(cast_term)?)),
                Term::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
                Term::Deref(deref_term) => self.eval_deref(deref_term),
                Term::Access(access_term) => Ok(ControlFlow::Break(self.eval_access(access_term)?)),

                // Imperative:
                Term::LoopControl(loop_control) => Err(self.eval_loop_control(loop_control)),
                Term::Assign(assign_term) => Ok(ControlFlow::Break(self.eval_assign(assign_term)?)),
                Term::Decl(decl_term) => self.eval_decl(decl_term),
                Term::Return(return_expr) => self.eval_return(return_expr)?,
                Term::Block(block_term) => Ok(ControlFlow::Break(self.eval_block(block_term)?)),
                Term::Loop(loop_term) => Ok(ControlFlow::Break(self.eval_loop(loop_term)?)),
            },
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Eval(term) => Ok(ControlFlow::Break(self.eval_ty_eval(term)?)),
                Ty::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
                Ty::Fn(_)
                | Ty::Tuple(_)
                | Ty::Data(_)
                | Ty::Universe(_)
                | Ty::Ref(_)
                | Ty::Hole(_) => Ok(ControlFlow::Break(atom)),
            },
            Atom::FnDef(_) => Ok(ControlFlow::Break(atom)),
            Atom::Pat(_) => Ok(ControlFlow::Continue(())),
        }
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_list(&self, term_list: TermListId, pat_list: PatListId) -> TermListId {
        // Create a new list term with the spread elements
        let spread_term_list = self.stores().pat_list().map_fast(pat_list, |pat_data| {
            self.stores().term_list().map_fast(term_list, |data| {
                pat_list
                    .to_index_range()
                    .filter_map(|i| match pat_data[i] {
                        PatOrCapture::Pat(_) => None,
                        PatOrCapture::Capture => Some(data[i]),
                    })
                    .collect_vec()
            })
        });
        self.new_term_list(spread_term_list)
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_args(&self, term_args: ArgsId, pat_args: PatArgsId) -> ArgsId {
        // Create a new tuple term with the spread elements
        let spread_term_args = self.stores().pat_args().map_fast(pat_args, |pat_data| {
            self.stores().args().map_fast(term_args, |data| {
                pat_args
                    .to_index_range()
                    .filter_map(|i| match pat_data[i].pat {
                        PatOrCapture::Pat(_) => None,
                        PatOrCapture::Capture => {
                            Some(ArgData { target: data[i].target, value: data[i].value })
                        }
                    })
                    .collect_vec()
            })
        });

        self.param_utils().create_args(spread_term_args.into_iter())
    }

    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    fn match_some_list_and_get_binds(
        &self,
        length: usize,
        spread: Option<Spread>,
        extract_spread_list: impl Fn(Spread) -> TermId,
        get_ith_pat: impl Fn(usize) -> PatOrCapture,
        get_ith_term: impl Fn(usize) -> TermId,
        f: &mut impl FnMut(StackMemberId, TermId),
    ) -> Result<MatchResult, Signal> {
        // We assume that the term list is well-typed with respect to the pattern list.

        let mut element_i = 0;
        while element_i < length {
            let arg_i = get_ith_term(element_i);
            let pat_arg_i = get_ith_pat(element_i);

            match pat_arg_i {
                PatOrCapture::Pat(pat_id) => {
                    match self.match_value_and_get_binds(arg_i, pat_id, f)? {
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
                }
                PatOrCapture::Capture => {
                    // Handled below
                }
            }

            element_i += 1;
        }

        // Capture the spread
        if let Some(spread) = spread {
            let spread_list = extract_spread_list(spread);
            if let Some(member) = spread.stack_member {
                f(member, spread_list);
            }
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
            term_args.len(),
            spread,
            |_| self.new_term(TupleTerm { data: self.extract_spread_args(term_args, pat_args) }),
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

    /// Check if the given atom is the `true` constructor.
    ///
    /// Assumes that the atom is normalised.
    fn is_true(&self, atom: Atom) -> bool {
        match atom {
            Atom::Term(term) => self.stores().term().map_fast(term, |term| match term {
                Term::Ctor(ctor_term) => ctor_term.ctor == self.get_bool_ctor(true),
                _ => false,
            }),
            Atom::Ty(_) | Atom::FnDef(_) | Atom::Pat(_) => false,
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

                    match self.match_value_and_get_binds(term_id, pat.assert_pat(), f)? {
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
                    list_term.elements.len(),
                    list_pat.spread,
                    |_| {
                        // Lists can have spreads, which return sublists
                        self.new_term(PrimTerm::List(ListCtor {
                            elements: self.extract_spread_list(list_term.elements, list_pat.pats),
                        }))
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
