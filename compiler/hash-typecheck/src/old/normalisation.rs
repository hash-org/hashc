//! Operations for normalising terms and types.
use std::{cell::Cell, ops::ControlFlow};

use hash_ast::ast::RangeEnd;
use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreId, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    intrinsics::utils::{get_bool_ctor, try_use_term_as_integer_lit},
    tir::{
        Arg, ArgsId, ArrayTerm, Lit, LitPat, Node, NodeId, NodesId, ParamIndex, Pat, PatArgsId,
        PatId, PatListId, PatOrCapture, RangePat, Spread, SymbolId, Term, TermId, TermListId,
        TupleTerm, Ty,
    },
    visitor::{Atom, Map, Visitor},
};
use hash_utils::itertools::Itertools;

use crate::{
    env::TcEnv,
    errors::TcResult,
    options::normalisation::{
        already_normalised, ctrl_continue, ctrl_map, normalisation_result_into, normalised_if,
        stuck_normalising, NormalisationMode, NormalisationState, NormaliseResult, NormaliseSignal,
    },
    tc::Tc,
    traits::Operations,
};

/// The result of matching a pattern against a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchResult {
    /// The pattern matched successfully.
    Successful,
    /// The pattern failed to match.
    Failed,
    /// The term could not be normalised enough to be matched.
    Stuck,
}

pub type FullEvaluation<T> = Result<T, NormaliseSignal>;

pub type AtomEvaluation = NormaliseResult<Atom>;

impl<'env, T: TcEnv + 'env> Tc<'env, T> {
    /// Normalise the given atom, in-place.
    ///
    /// returns `true` if the atom was normalised.
    pub fn normalise_in_place<N>(&self, atom: N) -> TcResult<bool>
    where
        Visitor: Map<N>,
        N: SingleStoreId,
    {
        if let Some(result) = self.potentially_normalise(atom)? {
            atom.set(result.value());
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Normalise the given atom.
    pub fn potentially_normalise<N>(&self, atom: N) -> TcResult<Option<N>>
    where
        Visitor: Map<N>,
    {
        match self.potentially_eval(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                NormaliseSignal::Break | NormaliseSignal::Continue | NormaliseSignal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                NormaliseSignal::Err(e) => Err(e),
            },
        }
    }

    /// Normalise the given atom.
    pub fn normalise_atom<N: Copy>(&self, atom: N) -> TcResult<N>
    where
        Visitor: Map<N>,
    {
        match self.eval(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                NormaliseSignal::Break | NormaliseSignal::Continue | NormaliseSignal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                NormaliseSignal::Err(e) => Err(e),
            },
        }
    }

    /// Evaluate an atom with the current mode, performing at least a single
    /// step of normalisation.
    pub fn eval<N: Copy>(&self, atom: N) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.potentially_eval(atom)? {
            Some(atom) => Ok(atom),
            None => Ok(atom),
        }
    }

    /// Same as `eval`, but also sets the `evaluated` flag in the given
    /// `EvalState`.
    pub fn eval_and_record<N: Copy>(
        &self,
        atom: N,
        state: &NormalisationState,
    ) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.potentially_eval(atom)? {
            Some(atom) => {
                state.set_normalised();
                Ok(atom)
            }
            None => Ok(atom),
        }
    }

    /// Evaluate an atom in full, even if it has no effects, and including
    /// impure function calls.
    fn eval_fully<N: Copy>(&self, atom: N) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        self.normalisation_opts.mode.enter(NormalisationMode::Full, || self.eval(atom))
    }

    /// Same as `eval_nested`, but with a given evaluation state.
    pub fn eval_nested_and_record<N: Copy>(
        &self,
        atom: N,
        state: &NormalisationState,
    ) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.normalisation_opts.mode.get() {
            NormalisationMode::Full => self.eval_and_record(atom, state),
            NormalisationMode::Weak => Ok(atom),
        }
    }

    /// Get the parameter at the given index in the given argument list.
    pub fn get_param_in_args(&self, args: ArgsId, target: ParamIndex) -> Atom {
        for arg_i in args.iter() {
            let arg = arg_i.value();
            if arg.target == target || ParamIndex::Position(arg_i.1) == target {
                return arg.value.into();
            }
        }
        panic!("Out of bounds index for access: {}", target)
    }

    /// Set the parameter at the given index in the given argument list.
    pub fn set_param_in_args(&self, args: ArgsId, target: ParamIndex, value: Atom) {
        let value = value.to_term();
        for arg_i in args.iter() {
            let arg = arg_i.value();
            if arg.target == target || ParamIndex::Position(arg_i.1) == target {
                arg_i.borrow_mut().value = value;
                return;
            }
        }
        panic!("Out of bounds index for access: {}", target)
    }

    /// Get the term at the given index in the given term list.
    ///
    /// Assumes that the index is normalised.
    pub fn get_index_in_array(&self, elements: TermListId, index: TermId) -> Option<Atom> {
        try_use_term_as_integer_lit::<_, usize>(self, index)
            .map(|idx| elements.elements().at(idx).unwrap().into())
    }

    /// Get the term at the given index in the given repeated array. If the
    /// index term is larger than the `repeat` count, we fail, otherwise
    /// return the `subject`.
    ///
    /// Assumes that the index is normalised.
    pub fn get_index_in_repeat(
        &self,
        subject: TermId,
        repeat: TermId,
        index: TermId,
    ) -> Option<Atom> {
        let subject = try_use_term_as_integer_lit::<_, usize>(self, subject)?;
        let index = try_use_term_as_integer_lit::<_, usize>(self, index)?;

        if index >= subject {
            None
        } else {
            Some(repeat.into())
        }
    }

    /// Evaluate an atom, performing at least a single step of normalisation.
    ///
    /// Returns `None` if the atom is already normalised.
    pub fn potentially_eval<N>(&self, atom: N) -> NormaliseResult<N>
    where
        Visitor: Map<N>,
    {
        let mut traversal = self.visitor();
        traversal.set_visit_fns_once(false);

        let st = NormalisationState::new();
        let nested = Cell::new(false);
        let result = traversal.try_map(atom, |atom| -> Result<_, NormaliseSignal> {
            let old_mode = if self.normalisation_opts.mode.get() == NormalisationMode::Weak
                && self.has_effects(atom) == Some(true)
            {
                // If the atom has effects, we need to evaluate it fully
                let old = self.normalisation_opts.mode.get();
                self.normalisation_opts.mode.set(NormalisationMode::Full);
                old
            } else {
                // Otherwise, we can just evaluate it normally
                self.normalisation_opts.mode.get()
            };

            let result = match self.eval_once(atom, nested.get())? {
                Some(result @ ControlFlow::Break(_)) => {
                    st.set_normalised();
                    Ok(result)
                }
                Some(result @ ControlFlow::Continue(())) => Ok(result),
                None => Ok(ControlFlow::Break(atom)),
            };

            self.normalisation_opts.mode.set(old_mode);

            if self.normalisation_opts.mode.get() == NormalisationMode::Weak {
                nested.set(true);
            }
            result
        })?;

        normalised_if(|| result, &st)
    }

    /// Evaluate an atom once, for use with `fmap`.
    ///
    /// Invariant: if `self.atom_has_effects(atom)`, then `self.eval_once(atom)
    /// != ctrl_continue()`.
    fn eval_once(&self, atom: Atom, nested: bool) -> NormaliseResult<ControlFlow<Atom>> {
        if nested && self.normalisation_opts.mode.get() == NormalisationMode::Weak {
            // If we're in weak mode, we don't want to evaluate nested atoms
            return already_normalised();
        }

        match atom {
            Atom::Term(term) => match *term.value() {
                Term::TyOf(ty_of_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(ty_of_term, term)))
                }
                Term::Unsafe(unsafe_expr) => {
                    ctrl_map(normalisation_result_into(self.normalise(unsafe_expr, term)))
                }
                Term::Match(match_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(match_term, term)))
                }
                Term::Call(fn_call) => {
                    ctrl_map(normalisation_result_into(self.normalise(fn_call, term)))
                }
                Term::Cast(cast_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(cast_term, term)))
                }
                Term::Hole(h) => ctrl_map(normalisation_result_into(self.normalise(h, term))),
                Term::Var(v) => ctrl_map(normalisation_result_into(self.normalise(v, term))),
                Term::Deref(deref_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(deref_term, term)))
                }
                Term::Access(access_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(access_term, term)))
                }
                Term::Index(index_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(index_term, term)))
                }

                // Introduction forms:
                Term::Ref(_)
                | Term::Intrinsic(_)
                | Term::Fn(_)
                | Term::Lit(_)
                | Term::Array(_)
                | Term::Tuple(_)
                | Term::Ctor(_) => ctrl_continue(),

                // Imperative:
                Term::LoopControl(loop_control) => {
                    ctrl_map(normalisation_result_into(self.normalise(loop_control, term)))
                }
                Term::Assign(assign_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(assign_term, term)))
                }
                Term::Return(return_expr) => {
                    ctrl_map(normalisation_result_into(self.normalise(return_expr, term)))
                }
                Term::Block(block_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(block_term, term)))
                }
                Term::Loop(loop_term) => {
                    ctrl_map(normalisation_result_into(self.normalise(loop_term, term)))
                }
                Ty::FnTy(_) | Ty::TupleTy(_) | Ty::DataTy(_) | Ty::Universe(_) | Ty::RefTy(_) => {
                    ctrl_continue()
                }
            },
            Atom::FnDef(_) => already_normalised(),
            Atom::Pat(_) => ctrl_continue(),
            Atom::Lit(_) => already_normalised(),
        }
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_list(&self, array_term: ArrayTerm, array_pat: PatListId) -> TermListId {
        // Create a new list term with the spread elements
        let spread_term_list = array_pat
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p {
                PatOrCapture::Pat(_) => None,
                PatOrCapture::Capture(_) => Some(array_term.element_at(i).unwrap()),
            })
            .collect_vec();
        Node::create_at(TermId::seq(spread_term_list), array_term.length_origin().computed())
    }

    /// From the given arguments matching with the given parameters, extract the
    /// arguments that are part of the given spread.
    fn extract_spread_args(&self, term_args: ArgsId, pat_args: PatArgsId) -> ArgsId {
        // Create a new tuple term with the spread elements
        let spread_term_args = pat_args
            .elements()
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p.pat {
                PatOrCapture::Pat(_) => None,
                PatOrCapture::Capture(_) => {
                    let arg = term_args.at(i).unwrap().value();
                    Some(Node::at(Arg { target: arg.target, value: arg.value }, arg.origin))
                }
            })
            .collect_vec();

        Node::create_at(Node::<Arg>::seq(spread_term_args), term_args.origin().computed())
    }

    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    fn match_some_array_and_get_binds(
        &self,
        length: usize,
        spread: Option<Spread>,
        extract_spread_list: impl Fn(Spread) -> TermId,
        get_ith_pat: impl Fn(usize) -> PatOrCapture,
        get_ith_term: impl Fn(usize) -> TermId,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
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
                PatOrCapture::Capture(_) => {
                    // Handled below
                }
            }

            element_i += 1;
        }

        // Capture the spread
        if let Some(spread) = spread {
            let spread_list = extract_spread_list(spread);
            f(spread.name, spread_list);
        }

        Ok(MatchResult::Successful)
    }

    fn eval_array_term_len(&self, array: ArrayTerm) -> NormaliseResult<usize> {
        let st = NormalisationState::new();

        match array {
            ArrayTerm::Normal(elements) => normalised_if(|| elements.len(), &st),
            ArrayTerm::Repeated(_, repeat) => {
                let evaluated = self.eval_fully(repeat.into())?;
                let Atom::Term(term) = evaluated else {
                    return stuck_normalising();
                };

                let Some(length) = try_use_term_as_integer_lit::<_, usize>(self, term) else {
                    return stuck_normalising();
                };

                normalised_if(|| length, &st)
            }
        }
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
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        self.match_some_array_and_get_binds(
            term_args.len(),
            spread,
            |sp| {
                Term::from(
                    TupleTerm { data: self.extract_spread_args(term_args, pat_args) },
                    sp.name.origin().computed(),
                )
            },
            |i| pat_args.at(i).unwrap().borrow().pat,
            |i| term_args.at(i).unwrap().borrow().value,
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
            Atom::Term(term) => match **term.borrow() {
                Term::Ctor(ctor_term) => ctor_term.ctor == get_bool_ctor(true),
                _ => false,
            },
            Atom::Lit(_) | Atom::FnDef(_) | Atom::Pat(_) => false,
        }
    }

    /// Match a literal between two endpoints.
    fn match_literal_to_range<U: PartialOrd>(
        &self,
        value: U,
        maybe_start: Option<U>,
        maybe_end: Option<U>,
        range_end: RangeEnd,
    ) -> MatchResult {
        // If the start isn't provided, we don't need to check
        // that the value is larger than the start, as it will
        // always succeed.
        if let Some(start) = maybe_start && start < value {
            return MatchResult::Failed;
        }

        // If the end isn't provided, we can assume that the subject will
        // always match.
        if range_end == RangeEnd::Included {
            if let Some(end) = maybe_end && end > value {
                MatchResult::Failed
            } else {
                MatchResult::Successful
            }
        } else if let Some(end) = maybe_end && end >= value {
            MatchResult::Failed
        } else {
            MatchResult::Successful
        }
    }

    /// Match the given value with the given pattern, running `f` every time a
    /// bind is discovered.
    ///
    /// The term must be normalised and well-typed with respect to the pattern.
    pub fn match_value_and_get_binds(
        &self,
        term_id: TermId,
        pat_id: PatId,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        let evaluated_id = self.eval(term_id)?;
        let evaluated = *evaluated_id.value();
        match (evaluated, *pat_id.value()) {
            (_, Pat::Or(pats)) => {
                // Try each alternative in turn:
                for pat in pats.alternatives.iter() {
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
                    let cond = self.eval_fully(if_pat.condition.into())?;
                    if self.is_true(cond) {
                        return Ok(MatchResult::Successful);
                    }
                }

                Ok(MatchResult::Failed)
            }

            // Bindings, always successful
            (_, Pat::Binding(binding)) => {
                f(binding.name, evaluated_id);
                Ok(MatchResult::Successful)
            }

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
            (Term::Lit(lit_term), Pat::Range(RangePat { lo, hi, end })) => {
                // If we know both of the range ends, then we can simply evaluate it
                // using the value. If not, we then create the `min` or `max` values
                // that are missing based on the type of the literal.

                // Disallow open excluded ranges to be parameterless. This isn't strictly
                // necessary, but it is strange to write `..<` and mean to match
                // everything but the end. This is checked and reported as an
                // error in untyped-semantics.
                if end == RangeEnd::Excluded {
                    debug_assert!(hi.is_some())
                }

                let lo = lo.map(|LitPat(lit)| *lit.value());
                let hi = hi.map(|LitPat(lit)| *lit.value());

                Ok(match (*lit_term.value(), lo, hi) {
                    (Lit::Int(value), Some(Lit::Int(lo)), Some(Lit::Int(hi))) => self
                        .match_literal_to_range(
                            value.value(),
                            Some(lo.value()),
                            Some(hi.value()),
                            end,
                        ),
                    (Lit::Char(value), Some(Lit::Char(lo)), Some(Lit::Char(hi))) => self
                        .match_literal_to_range(
                            value.value(),
                            Some(lo.value()),
                            Some(hi.value()),
                            end,
                        ),
                    (Lit::Int(value), Some(Lit::Int(lo)), None) => {
                        self.match_literal_to_range(value.value(), Some(lo.value()), None, end)
                    }
                    (Lit::Int(value), None, Some(Lit::Int(hi))) => {
                        self.match_literal_to_range(value.value(), None, Some(hi.value()), end)
                    }
                    (Lit::Char(value), Some(Lit::Char(lo)), None) => {
                        self.match_literal_to_range(value.value(), Some(lo.value()), None, end)
                    }
                    (Lit::Char(value), None, Some(Lit::Char(hi))) => {
                        self.match_literal_to_range(value.value(), None, Some(hi.value()), end)
                    }
                    _ => MatchResult::Stuck,
                })
            }
            (_, Pat::Range(_)) => Ok(MatchResult::Stuck),

            // Literals
            (Term::Lit(lit_term), Pat::Lit(lit_pat)) => {
                match (*lit_term.value(), *(*lit_pat).value()) {
                    (Lit::Int(a), Lit::Int(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    (Lit::Str(a), Lit::Str(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    (Lit::Char(a), Lit::Char(b)) => {
                        Ok(self.match_literal_to_literal(a.value(), b.value()))
                    }
                    _ => Ok(MatchResult::Stuck),
                }
            }
            // Arrays
            (Term::Array(array_term), Pat::Array(array_pat)) => {
                // Evaluate the length of the array term.
                let Some(length) = self.eval_array_term_len(array_term)? else {
                    return Ok(MatchResult::Stuck);
                };

                self.match_some_array_and_get_binds(
                    length,
                    array_pat.spread,
                    |sp| {
                        // Lists can have spreads, which return sublists
                        Term::from(
                            Term::Array(ArrayTerm::Normal(
                                self.extract_spread_list(array_term, array_pat.pats),
                            )),
                            sp.name.origin().computed(),
                        )
                    },
                    |i| array_pat.pats.elements().at(i).unwrap(),
                    |i| match array_term {
                        ArrayTerm::Normal(elements) => elements.elements().at(i).unwrap(),
                        ArrayTerm::Repeated(subject, _) => subject,
                    },
                    f,
                )
            }
            (_, Pat::Lit(_)) => Ok(MatchResult::Stuck),
            (_, Pat::Array(_)) => Ok(MatchResult::Stuck),
        }
    }
}
