//! Operations for normalising terms and types.
use std::{cell::Cell, ops::ControlFlow};

use derive_more::{Deref, From};
use hash_ast::ast::RangeEnd;
use hash_intrinsics::utils::PrimitiveUtils;
use hash_tir::{
    access::AccessTerm,
    args::{ArgData, ArgsId, PatArgsId, PatOrCapture},
    arrays::{ArrayTerm, IndexTerm},
    atom_info::ItemInAtomInfo,
    casting::CastTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    environment::context::ScopeKind,
    fns::{FnBody, FnCallTerm, FnDefId},
    holes::Hole,
    lits::{Lit, LitPat},
    params::ParamIndex,
    pats::{Pat, PatId, PatListId, Spread},
    refs::DerefTerm,
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    symbols::Symbol,
    terms::{Term, TermId, TermListId, UnsafeTerm},
    tuples::TupleTerm,
    tys::{Ty, TyId, TypeOfTerm},
    utils::{
        common::CommonUtils,
        traversing::{Atom, TraversingUtils},
        AccessToUtils,
    },
};
use hash_utils::{
    itertools::Itertools,
    log::info,
    store::{CloneStore, PartialStore, SequenceStore, SequenceStoreKey, Store},
};

use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking, IntrinsicAbilitiesWrapper,
};

#[derive(Deref)]
pub struct NormalisationOps<'a, T: AccessToTypechecking> {
    #[deref]
    env: &'a T,
    mode: Cell<NormalisationMode>,
}

/// The mode in which to normalise terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalisationMode {
    /// Normalise the term as much as possible.
    Full,
    /// Normalise the term to a single step.
    ///
    /// This will not execute any impure code.
    Weak,
}

/// Represents a normalisation result.
#[derive(Debug, Clone, From)]
pub enum Signal {
    Break,
    Continue,
    Return(Atom),
    Err(TcError),
}

/// The result of matching a pattern against a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MatchResult {
    /// The pattern matched successfully.
    Successful,
    /// The pattern failed to match.
    Failed,
    /// The term could not be normalised enough to be matched.
    Stuck,
}

pub type Evaluation<T> = Result<Option<T>, Signal>;
pub type FullEvaluation<T> = Result<T, Signal>;

pub type AtomEvaluation = Evaluation<Atom>;

fn already_evaluated<T>() -> Evaluation<T> {
    Ok(None)
}

fn stuck_evaluating<T>() -> Evaluation<T> {
    Ok(None)
}

fn evaluation_if<T, I: Into<T>>(atom: impl FnOnce() -> I, state: &EvalState) -> Evaluation<T> {
    if state.has_evaluated() {
        Ok(Some(atom().into()))
    } else {
        Ok(None)
    }
}

fn full_evaluation_to<T>(atom: impl Into<T>) -> FullEvaluation<T> {
    Ok(atom.into())
}

fn evaluation_to<T>(atom: impl Into<T>) -> Evaluation<T> {
    Ok(Some(atom.into()))
}

fn evaluation_option<T>(atom: Option<impl Into<T>>) -> Evaluation<T> {
    match atom {
        Some(eval) => evaluation_to(eval),
        None => already_evaluated(),
    }
}

fn ctrl_map_full<T>(t: FullEvaluation<T>) -> Evaluation<ControlFlow<T>> {
    Ok(Some(ControlFlow::Break(t?)))
}

fn ctrl_map<T>(t: Evaluation<T>) -> Evaluation<ControlFlow<T>> {
    Ok(t?.map(|t| ControlFlow::Break(t)))
}

fn ctrl_continue<T>() -> Evaluation<ControlFlow<T>> {
    Ok(Some(ControlFlow::Continue(())))
}

/// Whether a term has been evaluated or not.
pub struct EvalState {
    has_evaluated: Cell<bool>,
}

fn eval_state() -> EvalState {
    EvalState { has_evaluated: Cell::new(false) }
}

impl EvalState {
    fn has_evaluated(&self) -> bool {
        self.has_evaluated.get()
    }

    fn set_evaluated(&self) {
        self.has_evaluated.set(true);
    }

    fn update_from_evaluation<T>(
        &self,
        previous: T,
        evaluation: Evaluation<T>,
    ) -> Result<T, Signal> {
        if let Ok(Some(new)) = evaluation {
            self.set_evaluated();
            Ok(new)
        } else if let Err(e) = evaluation {
            Err(e)
        } else {
            Ok(previous)
        }
    }
}

impl<'tc, T: AccessToTypechecking> NormalisationOps<'tc, T> {
    pub fn new(env: &'tc T) -> Self {
        Self { env, mode: Cell::new(NormalisationMode::Weak) }
    }

    /// Change the normalisation mode.
    pub fn with_mode(&self, mode: NormalisationMode) -> &Self {
        self.mode.set(mode);
        self
    }

    /// Normalise the given atom, in-place.
    ///
    /// returns `true` if the atom was normalised.
    pub fn normalise_in_place(&self, atom: Atom) -> TcResult<bool> {
        if let Some(result) = self.potentially_normalise(atom)? {
            match atom {
                Atom::Term(term_id) => {
                    self.stores().term().set(term_id, self.get_term(self.to_term(result)));
                }
                Atom::Ty(ty_id) => {
                    self.stores().ty().set(ty_id, self.get_ty(self.to_ty(result)));
                }
                // Fn defs are already normalised.
                Atom::FnDef(_) => return Ok(false),
                Atom::Pat(pat_id) => {
                    self.stores().pat().set(pat_id, self.get_pat(self.to_pat(result)));
                }
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Normalise the given atom.
    pub fn potentially_normalise(&self, atom: Atom) -> TcResult<Option<Atom>> {
        match self.potentially_eval(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                Signal::Break | Signal::Continue | Signal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                Signal::Err(e) => Err(e),
            },
        }
    }

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
            Atom::Term(term) => self.try_use_term_as_ty(term),
            Atom::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    /// Normalise the given atom, and try to use it as a function definition.
    pub fn maybe_to_fn_def(&self, atom: Atom) -> Option<FnDefId> {
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                Term::FnRef(fn_def_id) => Some(fn_def_id),
                _ => None,
            },
            Atom::FnDef(fn_def_id) => Some(fn_def_id),
            _ => None,
        }
    }

    /// Normalise the given atom, and try to use it as a term.
    pub fn maybe_to_term(&self, atom: Atom) -> Option<TermId> {
        match atom {
            Atom::Term(term) => Some(term),
            Atom::Ty(ty) => Some(self.use_ty_as_term(ty)),
            Atom::FnDef(fn_def_id) => Some(self.new_term(fn_def_id)),
            _ => None,
        }
    }

    /// Normalise the given atom, and try to use it as a pattern.
    pub fn maybe_to_pat(&self, atom: Atom) -> Option<PatId> {
        match atom {
            Atom::Pat(pat) => Some(pat),
            _ => None,
        }
    }

    /// Normalise the given atom, and try to use it as a term.
    pub fn to_term(&self, atom: Atom) -> TermId {
        self.maybe_to_term(atom)
            .unwrap_or_else(|| panic!("Cannot convert {} to a term", self.env().with(atom)))
    }

    /// Normalise the given atom, and try to use it as a function definition.
    pub fn to_fn_def(&self, atom: Atom) -> FnDefId {
        self.maybe_to_fn_def(atom)
            .unwrap_or_else(|| panic!("Cannot convert {} to an fn def", self.env().with(atom)))
    }

    /// Try to use the given atom as a type.
    pub fn to_ty(&self, atom: Atom) -> TyId {
        self.maybe_to_ty(atom)
            .unwrap_or_else(|| panic!("Cannot convert {} to a type", self.env().with(atom)))
    }

    /// Try to use the given atom as a pattern.
    pub fn to_pat(&self, atom: Atom) -> PatId {
        self.maybe_to_pat(atom)
            .unwrap_or_else(|| panic!("Cannot convert {} to a pattern", self.env().with(atom)))
    }

    fn atom_has_effects_once(
        &self,
        traversing_utils: &TraversingUtils,
        atom: Atom,
        has_effects: &mut Option<bool>,
    ) -> Result<ControlFlow<()>, !> {
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                // Never has effects
                Term::Hole(_) | Term::FnRef(_) => Ok(ControlFlow::Break(())),

                // These have effects if their constituents do
                Term::Lit(_)
                | Term::Ctor(_)
                | Term::Tuple(_)
                | Term::Var(_)
                | Term::Match(_)
                | Term::Decl(_)
                | Term::Unsafe(_)
                | Term::Access(_)
                | Term::Array(_)
                | Term::Index(_)
                | Term::Cast(_)
                | Term::TypeOf(_)
                | Term::Ty(_)
                | Term::Block(_) => Ok(ControlFlow::Continue(())),

                Term::FnCall(fn_call) => {
                    // Get its inferred type and check if it is pure
                    match self.try_get_inferred_ty(fn_call.subject) {
                        Some(fn_ty) => {
                            match self.get_ty(fn_ty) {
                                Ty::Fn(fn_ty) => {
                                    // If it is a function, check if it is pure
                                    if fn_ty.pure {
                                        // Check its args too
                                        traversing_utils
                                            .visit_args::<!, _>(fn_call.args, &mut |atom| {
                                                self.atom_has_effects_once(
                                                    traversing_utils,
                                                    atom,
                                                    has_effects,
                                                )
                                            })
                                            .into_ok();
                                        Ok(ControlFlow::Break(()))
                                    } else {
                                        *has_effects = Some(true);
                                        Ok(ControlFlow::Break(()))
                                    }
                                }
                                _ => {
                                    // If it is not a function, it is a function reference, which is
                                    // pure
                                    info!(
                                        "Found a function term that is not typed as a function: {}",
                                        self.env().with(fn_call.subject)
                                    );
                                    Ok(ControlFlow::Break(()))
                                }
                            }
                        }
                        None => {
                            // Unknown
                            *has_effects = None;
                            Ok(ControlFlow::Break(()))
                        }
                    }
                }

                // These always have effects
                Term::Ref(_)
                | Term::Deref(_)
                | Term::Assign(_)
                | Term::Loop(_)
                | Term::LoopControl(_)
                | Term::Return(_) => {
                    *has_effects = Some(true);
                    Ok(ControlFlow::Break(()))
                }
            },
            Atom::Ty(_) => Ok(ControlFlow::Continue(())),
            Atom::FnDef(fn_def_id) => {
                let fn_ty = self.get_fn_def(fn_def_id).ty;
                // Check its params and return type only (no body)
                traversing_utils.visit_params(fn_ty.params, &mut |atom| {
                    self.atom_has_effects_once(traversing_utils, atom, has_effects)
                })?;
                traversing_utils.visit_ty(fn_ty.return_ty, &mut |atom| {
                    self.atom_has_effects_once(traversing_utils, atom, has_effects)
                })?;
                Ok(ControlFlow::Break(()))
            }
            Atom::Pat(_) => Ok(ControlFlow::Continue(())),
        }
    }

    /// Whether the given atom will produce effects when evaluated.
    pub fn atom_has_effects_with_traversing(
        &self,
        atom: Atom,
        traversing_utils: &TraversingUtils,
    ) -> Option<bool> {
        let mut has_effects = Some(false);
        traversing_utils
            .visit_atom::<!, _>(atom, &mut |atom| {
                self.atom_has_effects_once(traversing_utils, atom, &mut has_effects)
            })
            .into_ok();
        has_effects
    }

    /// Whether the given atom will produce effects when evaluated.
    pub fn atom_has_effects(&self, atom: Atom) -> Option<bool> {
        self.atom_has_effects_with_traversing(atom, &self.traversing_utils())
    }

    /// Evaluate an atom with the current mode, performing at least a single
    /// step of normalisation.
    fn eval(&self, atom: Atom) -> Result<Atom, Signal> {
        match self.potentially_eval(atom)? {
            Some(atom) => Ok(atom),
            None => Ok(atom),
        }
    }

    /// Same as `eval`, but also sets the `evaluated` flag in the given
    /// `EvalState`.
    fn eval_and_record(&self, atom: Atom, state: &EvalState) -> Result<Atom, Signal> {
        match self.potentially_eval(atom)? {
            Some(atom) => {
                state.set_evaluated();
                Ok(atom)
            }
            None => Ok(atom),
        }
    }

    /// Evaluate an atom in full, even if it has no effects, and including
    /// impure function calls.
    fn eval_fully(&self, atom: Atom) -> Result<Atom, Signal> {
        let old_mode = self.mode.replace(NormalisationMode::Full);
        let result = self.eval(atom);
        self.mode.set(old_mode);
        result
    }

    /// Same as `eval_nested`, but with a given evaluation state.
    fn eval_nested_and_record(&self, atom: Atom, state: &EvalState) -> Result<Atom, Signal> {
        match self.mode.get() {
            NormalisationMode::Full => self.eval_and_record(atom, state),
            NormalisationMode::Weak => Ok(atom),
        }
    }

    /// Evaluate a block term.
    fn eval_block(&self, block_term: BlockTerm) -> AtomEvaluation {
        self.context().enter_scope(ScopeKind::Stack(block_term.stack_id), || {
            let st = eval_state();

            for statement in block_term
                .statements
                .to_index_range()
                .map(|i| self.stores().term_list().get_at_index(block_term.statements, i))
            {
                let _ = self.eval_and_record(statement.into(), &st)?;
            }

            let sub = self.sub_ops().create_sub_from_current_scope();
            let result_term = self.eval_and_record(block_term.return_value.into(), &st)?;
            let subbed_result_term = self.sub_ops().apply_sub_to_atom(result_term, &sub);

            evaluation_to(subbed_result_term)
        })
    }

    /// Evaluate a variable.
    fn eval_var(&self, var: Symbol) -> AtomEvaluation {
        match self.context_utils().try_get_binding_value(var) {
            Some(result) => {
                if matches!(self.get_term(result), Term::Var(v) if v == var) {
                    already_evaluated()
                } else {
                    evaluation_to(self.eval(result.into())?)
                }
            }
            None => already_evaluated(),
        }
    }

    /// Evaluate a cast term.
    fn eval_cast(&self, cast_term: CastTerm) -> AtomEvaluation {
        // @@Todo: will not play well with typeof?;
        evaluation_option(self.potentially_eval(cast_term.subject_term.into())?)
    }

    /// Evaluate a dereference term.
    fn eval_deref(&self, mut deref_term: DerefTerm) -> AtomEvaluation {
        let st = eval_state();
        deref_term.subject = self.to_term(self.eval_and_record(deref_term.subject.into(), &st)?);

        // Reduce:
        if let Term::Ref(ref_expr) = self.get_term(deref_term.subject) {
            // Should never be effectful
            return evaluation_to(ref_expr.subject);
        }

        evaluation_if(|| self.new_term(deref_term), &st)
    }

    /// Get the parameter at the given index in the given argument list.
    fn get_param_in_args(&self, args: ArgsId, target: ParamIndex) -> Atom {
        for arg_i in args.iter() {
            let arg = self.stores().args().get_element(arg_i);
            if arg.target == target || ParamIndex::Position(arg.id.1) == target {
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
            if arg.target == target || ParamIndex::Position(arg.id.1) == target {
                self.stores().args().modify_fast(arg_i.0, |mut args| args[arg_i.1].value = value);
                return;
            }
        }
        panic!("Out of bounds index for access: {}", self.env().with(target))
    }

    /// Get the term at the given index in the given term list.
    ///
    /// Assumes that the index is normalised.
    fn get_index_in_array(&self, elements: TermListId, index: TermId) -> Option<Atom> {
        self.try_use_term_as_integer_lit::<usize>(index)
            .map(|idx| self.stores().term_list().get_at_index(elements, idx).into())
    }

    /// Evaluate an access term.
    fn eval_access(&self, mut access_term: AccessTerm) -> AtomEvaluation {
        let st = eval_state();
        access_term.subject = self.to_term(self.eval_and_record(access_term.subject.into(), &st)?);

        let result = match self.get_term(access_term.subject) {
            Term::Tuple(tuple) => self.get_param_in_args(tuple.data, access_term.field),
            Term::Ctor(ctor) => self.get_param_in_args(ctor.ctor_args, access_term.field),
            _ => {
                return stuck_evaluating();
            }
        };

        let result = self.eval_and_record(result, &st)?;
        evaluation_if(|| result, &st)
    }

    /// Evaluate an index term.
    fn eval_index(&self, mut index_term: IndexTerm) -> AtomEvaluation {
        let st = eval_state();
        index_term.subject = self.to_term(self.eval_and_record(index_term.subject.into(), &st)?);

        if let Term::Array(arr) = self.get_term(index_term.subject) &&
           let Some(result) = self.get_index_in_array(arr.elements, index_term.index)
        {
            let result = self.eval_and_record(result, &st)?;
            evaluation_if(|| result, &st)
        } else {
            stuck_evaluating()
        }
    }

    /// Evaluate an unsafe term.
    fn eval_unsafe(&self, unsafe_term: UnsafeTerm) -> AtomEvaluation {
        // @@Todo: handle unsafe safety
        evaluation_option(self.potentially_eval(unsafe_term.inner.into())?)
    }

    /// Evaluate a `typeof` term.
    fn eval_type_of(&self, type_of_term: TypeOfTerm) -> AtomEvaluation {
        // Infer the type of the term:
        match self.try_get_inferred_ty(type_of_term.term) {
            Some(ty) => evaluation_to(ty),
            None => {
                // Not evaluated yet
                stuck_evaluating()
            }
        }
    }

    /// Evaluate a loop control term.
    fn eval_loop_control(&self, loop_control_term: LoopControlTerm) -> Signal {
        match loop_control_term {
            LoopControlTerm::Break => Signal::Break,
            LoopControlTerm::Continue => Signal::Continue,
        }
    }

    /// Evaluate an assignment term.
    fn eval_assign(&self, mut assign_term: AssignTerm) -> FullEvaluation<Atom> {
        assign_term.value = self.to_term(self.eval(assign_term.value.into())?);

        match self.get_term(assign_term.subject) {
            Term::Access(mut access_term) => {
                access_term.subject = self.to_term(self.eval(access_term.subject.into())?);
                match self.get_term(access_term.subject) {
                    Term::Tuple(tuple) => self.set_param_in_args(
                        tuple.data,
                        access_term.field,
                        assign_term.value.into(),
                    ),
                    Term::Ctor(ctor) => self.set_param_in_args(
                        ctor.ctor_args,
                        access_term.field,
                        assign_term.value.into(),
                    ),
                    _ => panic!("Invalid access"),
                }
            }
            Term::Var(var) => {
                self.context_utils().modify_assignment(var, assign_term.value);
            }
            _ => panic!("Invalid assign {}", self.env().with(&assign_term)),
        }

        full_evaluation_to(self.new_void_term())
    }

    /// Evaluate a match term.
    fn eval_match(&self, mut match_term: MatchTerm) -> AtomEvaluation {
        let st = eval_state();
        match_term.subject = self.to_term(self.eval_and_record(match_term.subject.into(), &st)?);

        for case_id in match_term.cases.iter() {
            let case = self.stores().match_cases().get_element(case_id);
            let mut outcome = None;

            self.context().enter_scope(case.stack_id.into(), || -> Result<(), Signal> {
                match self.match_value_and_get_binds(
                    match_term.subject,
                    case.bind_pat,
                    &mut |name, term_id| self.context_utils().add_untyped_assignment(name, term_id),
                )? {
                    MatchResult::Successful => {
                        let result = self.eval_and_record(case.value.into(), &st)?;
                        outcome = Some(evaluation_to(result));
                    }
                    MatchResult::Failed => {}
                    MatchResult::Stuck => {
                        outcome = Some(stuck_evaluating());
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
    fn eval_decl(&self, mut decl_term: DeclTerm) -> AtomEvaluation {
        let st = eval_state();
        decl_term.value = decl_term
            .value
            .map(|v| -> Result<_, Signal> {
                Ok(self.to_term(self.eval_nested_and_record(v.into(), &st)?))
            })
            .transpose()?;

        match decl_term.value {
            Some(value) => match self.match_value_and_get_binds(
                value,
                decl_term.bind_pat,
                &mut |name, term_id| self.context_utils().add_untyped_assignment(name, term_id),
            )? {
                MatchResult::Successful => {
                    // All good
                    evaluation_to(self.new_void_term())
                }
                MatchResult::Failed => {
                    panic!("Non-exhaustive let-binding: {}", self.env().with(&decl_term))
                }
                MatchResult::Stuck => {
                    info!("Stuck evaluating let-binding: {}", self.env().with(&decl_term));
                    evaluation_if(|| self.new_term(decl_term), &st)
                }
            },
            None => {
                panic!("Let binding with no value: {}", self.env().with(&decl_term))
            }
        }
    }

    /// Evaluate a `return` term.
    fn eval_return(&self, return_term: ReturnTerm) -> Result<!, Signal> {
        let normalised = self.eval(return_term.expression.into())?;
        Err(Signal::Return(normalised))
    }

    /// Evaluate a `loop` term.
    fn eval_loop(&self, loop_term: LoopTerm) -> FullEvaluation<Atom> {
        loop {
            match self.eval_block(loop_term.block) {
                Ok(_) | Err(Signal::Continue) => continue,
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        full_evaluation_to(self.new_void_term())
    }

    /// Evaluate a term and use it as a type.
    fn eval_ty_eval(&self, term: TermId) -> AtomEvaluation {
        let st = eval_state();
        let evaluated = self.eval_and_record(term.into(), &st)?;
        match evaluated {
            Atom::Ty(_) => evaluation_to(evaluated),
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => evaluation_to(Atom::Ty(ty)),
                _ => evaluation_if(|| term, &st),
            },
            Atom::FnDef(_) | Atom::Pat(_) => unreachable!(),
        }
    }

    /// Evaluate some arguments
    fn eval_args(&self, args: ArgsId) -> Evaluation<ArgsId> {
        let args = self.stores().args().get_vec(args);
        let st = eval_state();

        let evaluated_arg_data = args
            .into_iter()
            .map(|arg| -> Result<_, Signal> {
                Ok(ArgData {
                    target: arg.target,
                    value: self.to_term(self.eval_nested_and_record(arg.value.into(), &st)?),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        evaluation_if(|| self.param_utils().create_args(evaluated_arg_data.into_iter()), &st)
    }

    /// Evaluate a function call.
    fn eval_fn_call(&self, mut fn_call: FnCallTerm) -> AtomEvaluation {
        let st = eval_state();

        fn_call.subject = self.to_term(self.eval_and_record(fn_call.subject.into(), &st)?);
        fn_call.args = st.update_from_evaluation(fn_call.args, self.eval_args(fn_call.args))?;

        // Beta-reduce:
        if let Term::FnRef(fn_def_id) = self.get_term(fn_call.subject) {
            let fn_def = self.get_fn_def(fn_def_id);
            if (fn_def.ty.pure || matches!(self.mode.get(), NormalisationMode::Full))
                && self.try_get_inferred_ty(fn_def_id).is_some()
            {
                match fn_def.body {
                    FnBody::Defined(defined_fn_def) => {
                        return self.context().enter_scope(fn_def_id.into(), || {
                            // Add argument bindings:
                            self.context_utils().add_arg_bindings(fn_def.ty.params, fn_call.args);

                            // Evaluate result:
                            match self.eval(defined_fn_def.into()) {
                                Err(Signal::Return(result)) | Ok(result) => {
                                    // Substitute remaining bindings:
                                    let sub = self.sub_ops().create_sub_from_current_scope();
                                    let result = self.sub_ops().apply_sub_to_atom(result, &sub);
                                    evaluation_to(result)
                                }
                                Err(e) => Err(e),
                            }
                        });
                    }

                    FnBody::Intrinsic(intrinsic_id) => {
                        return self.context().enter_scope(fn_def_id.into(), || {
                            let args_as_terms =
                                self.stores().args().map_fast(fn_call.args, |args| {
                                    args.iter().map(|arg| arg.value).collect_vec()
                                });

                            // Run intrinsic:
                            let result: TermId = self
                                .intrinsics()
                                .implementations
                                .map_fast(intrinsic_id, |intrinsic| {
                                    let intrinsic = intrinsic.unwrap();
                                    (intrinsic.implementation)(
                                        &IntrinsicAbilitiesWrapper { tc: self.env },
                                        &args_as_terms,
                                    )
                                })
                                .map_err(TcError::Intrinsic)?;

                            evaluation_to(result)
                        });
                    }

                    FnBody::Axiom => {
                        // Nothing further to do
                    }
                }
            }
        }

        evaluation_if(|| self.new_term(fn_call), &st)
    }

    /// Evaluate an atom, performing at least a single step of normalisation.
    ///
    /// Returns `None` if the atom is already normalised.
    fn potentially_eval(&self, atom: Atom) -> AtomEvaluation {
        let mut traversal = self.traversing_utils();
        traversal.set_visit_fns_once(false);

        let st = eval_state();
        let nested = Cell::new(false);
        let result = traversal.fmap_atom(atom, |atom| -> Result<_, Signal> {
            let old_mode = if self.mode.get() == NormalisationMode::Weak
                && self.atom_has_effects(atom) == Some(true)
            {
                // If the atom has effects, we need to evaluate it fully
                self.mode.replace(NormalisationMode::Full)
            } else {
                // Otherwise, we can just evaluate it normally
                self.mode.get()
            };

            let result = match self.eval_once(atom, nested.get())? {
                Some(result @ ControlFlow::Break(_)) => {
                    st.set_evaluated();
                    Ok(result)
                }
                Some(result @ ControlFlow::Continue(())) => Ok(result),
                None => Ok(ControlFlow::Break(atom)),
            };

            self.mode.set(old_mode);

            if self.mode.get() == NormalisationMode::Weak {
                nested.set(true);
            }
            result
        })?;

        self.stores().location().copy_location(atom, result);
        evaluation_if(|| result, &st)
    }

    /// Evaluate an atom once, for use with `fmap`.
    ///
    /// Invariant: if `self.atom_has_effects(atom)`, then `self.eval_once(atom)
    /// != ctrl_continue()`.
    fn eval_once(&self, atom: Atom, nested: bool) -> Evaluation<ControlFlow<Atom>> {
        if nested && self.mode.get() == NormalisationMode::Weak {
            // If we're in weak mode, we don't want to evaluate nested atoms
            return already_evaluated();
        }

        match atom {
            Atom::Term(term) => match self.get_term(term) {
                // Types
                Term::Ty(_) => ctrl_continue(),

                Term::TypeOf(term) => ctrl_map(self.eval_type_of(term)),
                Term::Unsafe(unsafe_expr) => ctrl_map(self.eval_unsafe(unsafe_expr)),
                Term::Match(match_term) => ctrl_map(self.eval_match(match_term)),
                Term::FnCall(fn_call) => ctrl_map(self.eval_fn_call(fn_call)),
                Term::Cast(cast_term) => ctrl_map(self.eval_cast(cast_term)),
                Term::Hole(Hole(var)) | Term::Var(var) => ctrl_map(self.eval_var(var)),
                Term::Deref(deref_term) => ctrl_map(self.eval_deref(deref_term)),
                Term::Access(access_term) => ctrl_map(self.eval_access(access_term)),
                Term::Index(index_term) => ctrl_map(self.eval_index(index_term)),

                // Introduction forms:
                Term::Ref(_)
                | Term::FnRef(_)
                | Term::Lit(_)
                | Term::Array(_)
                | Term::Tuple(_)
                | Term::Ctor(_) => ctrl_continue(),

                // Imperative:
                Term::LoopControl(loop_control) => Err(self.eval_loop_control(loop_control)),
                Term::Assign(assign_term) => ctrl_map_full(self.eval_assign(assign_term)),
                Term::Decl(decl_term) => ctrl_map(self.eval_decl(decl_term)),
                Term::Return(return_expr) => self.eval_return(return_expr)?,
                Term::Block(block_term) => ctrl_map(self.eval_block(block_term)),
                Term::Loop(loop_term) => ctrl_map_full(self.eval_loop(loop_term)),
            },
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Eval(term) => ctrl_map(self.eval_ty_eval(term)),
                Ty::Hole(Hole(var)) | Ty::Var(var) => ctrl_map(self.eval_var(var)),
                Ty::Fn(_) | Ty::Tuple(_) | Ty::Data(_) | Ty::Universe(_) | Ty::Ref(_) => {
                    ctrl_continue()
                }
            },
            Atom::FnDef(_) => already_evaluated(),
            Atom::Pat(_) => ctrl_continue(),
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
        f: &mut impl FnMut(Symbol, TermId),
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
            f(spread.name, spread_list);
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
        f: &mut impl FnMut(Symbol, TermId),
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
        f: &mut impl FnMut(Symbol, TermId),
    ) -> Result<MatchResult, Signal> {
        let evaluated_id = self.to_term(self.eval(term_id.into())?);
        let evaluated = self.get_term(evaluated_id);
        match (evaluated, self.get_pat(pat_id)) {
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
            (Term::Lit(lit_term), Pat::Range(range_pat)) => {
                match (lit_term, range_pat.start, range_pat.end) {
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
                }
            }
            (_, Pat::Range(_)) => Ok(MatchResult::Stuck),

            // Literals
            (Term::Lit(lit_term), Pat::Lit(lit_pat)) => match (lit_term, lit_pat) {
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
            // Lists
            (Term::Array(array_term), Pat::Array(list_pat)) => self.match_some_list_and_get_binds(
                array_term.elements.len(),
                list_pat.spread,
                |_| {
                    // Lists can have spreads, which return sublists
                    self.new_term(Term::Array(ArrayTerm {
                        elements: self.extract_spread_list(array_term.elements, list_pat.pats),
                    }))
                },
                |i| self.stores().pat_list().get_at_index(list_pat.pats, i),
                |i| self.stores().term_list().get_at_index(array_term.elements, i),
                f,
            ),
            (_, Pat::Lit(_)) => Ok(MatchResult::Stuck),
            (_, Pat::Array(_)) => Ok(MatchResult::Stuck),
        }
    }
}
