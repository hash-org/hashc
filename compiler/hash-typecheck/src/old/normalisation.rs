//! Operations for normalising terms and types.
use std::{cell::Cell, ops::ControlFlow};

use hash_ast::ast::RangeEnd;
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{Context, ScopeKind},
    intrinsics::{
        make::IsIntrinsic,
        utils::{get_bool_ctor, try_use_term_as_integer_lit},
    },
    scopes::{AssignTerm, BlockStatement, BlockTerm},
    stores::tir_stores,
    tir::{
        AccessTerm, Arg, ArgsId, ArrayTerm, CallTerm, CastTerm, DerefTerm, FnDefId, Hole,
        IndexTerm, Lit, LitPat, LoopControlTerm, LoopTerm, MatchTerm, Node, NodeId, NodesId,
        ParamIndex, Pat, PatArgsId, PatId, PatListId, PatOrCapture, RangePat, ReturnTerm, Spread,
        SymbolId, Term, TermId, TermListId, TupleTerm, Ty, TyId, TyOfTerm, UnsafeTerm, VarTerm,
    },
    visitor::{Atom, Map, Visit, Visitor},
};
use hash_utils::{derive_more::Deref, itertools::Itertools, log::info};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult},
    intrinsic_abilities::IntrinsicAbilitiesImpl,
    operations::{
        normalisation::{
            already_normalised, ctrl_continue, ctrl_map, normalised_if, normalised_option,
            normalised_to, stuck_normalising, NormalisationMode, NormalisationState,
            NormaliseResult, NormaliseSignal,
        },
        Operations,
    },
};

#[derive(Deref)]
pub struct NormalisationOps<'env, T: TcEnv> {
    #[deref]
    env: &'env T,
    mode: Cell<NormalisationMode>,
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

pub type FullEvaluation<T> = Result<T, NormaliseSignal>;

pub type AtomEvaluation = NormaliseResult<Atom>;

fn full_evaluation_to<T>(atom: impl Into<T>) -> FullEvaluation<T> {
    Ok(atom.into())
}

fn ctrl_map_full<T>(t: FullEvaluation<T>) -> NormaliseResult<ControlFlow<T>> {
    Ok(Some(ControlFlow::Break(t?)))
}

impl<'env, T: TcEnv + 'env> NormalisationOps<'env, T> {
    pub fn new(env: &'env T) -> Self {
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
                    term_id.set(self.to_term(result).value());
                }
                // Fn defs are already normalised.
                Atom::FnDef(_) => return Ok(false),
                Atom::Pat(pat_id) => {
                    pat_id.set(self.to_pat(result).value());
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
                NormaliseSignal::Break | NormaliseSignal::Continue | NormaliseSignal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                NormaliseSignal::Err(e) => Err(e),
            },
        }
    }

    /// Normalise the given atom.
    pub fn normalise(&self, atom: Atom) -> TcResult<Atom> {
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

    /// Try to use the given atom as a type.
    pub fn maybe_to_ty(&self, atom: Atom) -> Option<TyId> {
        match atom {
            Atom::Term(term) => Some(term),
            _ => None,
        }
    }

    /// Normalise the given atom, and try to use it as a function definition.
    pub fn maybe_to_fn_def(&self, atom: Atom) -> Option<FnDefId> {
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Fn(fn_def_id) => Some(fn_def_id),
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
            Atom::FnDef(fn_def_id) => Some(Term::from(fn_def_id, fn_def_id.origin())),
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
        self.maybe_to_term(atom).unwrap_or_else(|| panic!("Cannot convert {} to a term", atom))
    }

    /// Normalise the given atom, and try to use it as a function definition.
    pub fn to_fn_def(&self, atom: Atom) -> FnDefId {
        self.maybe_to_fn_def(atom).unwrap_or_else(|| panic!("Cannot convert {} to an fn def", atom))
    }

    /// Try to use the given atom as a type.
    pub fn to_ty(&self, atom: Atom) -> TyId {
        self.maybe_to_ty(atom).unwrap_or_else(|| panic!("Cannot convert {} to a type", atom))
    }

    /// Try to use the given atom as a pattern.
    pub fn to_pat(&self, atom: Atom) -> PatId {
        self.maybe_to_pat(atom).unwrap_or_else(|| panic!("Cannot convert {} to a pattern", atom))
    }

    fn atom_has_effects_once(
        traversing_utils: &Visitor,
        atom: Atom,
        has_effects: &mut Option<bool>,
    ) -> ControlFlow<()> {
        match atom {
            Atom::Term(term) => match *term.value() {
                // Never has effects
                Term::Intrinsic(_) | Term::Hole(_) | Term::Fn(_) => ControlFlow::Break(()),

                // These have effects if their constituents do
                Term::Lit(_)
                | Term::Ctor(_)
                | Term::Tuple(_)
                | Term::Var(_)
                | Term::Match(_)
                | Term::Unsafe(_)
                | Term::Access(_)
                | Term::Array(_)
                | Term::Index(_)
                | Term::Cast(_)
                | Term::TypeOf(_)
                | Term::DataTy(_)
                | Term::RefTy(_)
                | Term::Universe
                | Term::TupleTy(_)
                | Term::FnTy(_)
                | Term::Block(_) => ControlFlow::Continue(()),

                Term::Call(fn_call) => {
                    // Get its inferred type and check if it is pure
                    match tir_stores().atom_info().try_get_inferred_ty(fn_call.subject) {
                        Some(fn_ty) => {
                            match *fn_ty.value() {
                                Ty::FnTy(fn_ty) => {
                                    // If it is a function, check if it is pure
                                    if fn_ty.pure {
                                        // Check its args too
                                        traversing_utils.visit(fn_call.args, &mut |atom| {
                                            Self::atom_has_effects_once(
                                                traversing_utils,
                                                atom,
                                                has_effects,
                                            )
                                        });
                                        ControlFlow::Break(())
                                    } else {
                                        *has_effects = Some(true);
                                        ControlFlow::Break(())
                                    }
                                }
                                _ => {
                                    // If it is not a function, it is a function reference, which is
                                    // pure
                                    info!(
                                        "Found a function term that is not typed as a function: {}",
                                        fn_call.subject
                                    );
                                    ControlFlow::Break(())
                                }
                            }
                        }
                        None => {
                            // Unknown
                            *has_effects = None;
                            ControlFlow::Break(())
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
                    ControlFlow::Break(())
                }
            },
            Atom::FnDef(fn_def_id) => {
                let fn_ty = fn_def_id.value().ty;
                // Check its params and return type only (no body)
                traversing_utils.visit(fn_ty.params, &mut |atom| {
                    Self::atom_has_effects_once(traversing_utils, atom, has_effects)
                });
                traversing_utils.visit(fn_ty.return_ty, &mut |atom| {
                    Self::atom_has_effects_once(traversing_utils, atom, has_effects)
                });
                ControlFlow::Break(())
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
        }
    }

    /// Whether the given atom will produce effects when evaluated.
    pub fn atom_has_effects_with_traversing(
        &self,
        atom: Atom,
        traversing_utils: &Visitor,
    ) -> Option<bool> {
        let mut has_effects = Some(false);
        traversing_utils.visit(atom, &mut |atom| {
            Self::atom_has_effects_once(traversing_utils, atom, &mut has_effects)
        });
        has_effects
    }

    /// Whether the given atom will produce effects when evaluated.
    pub fn atom_has_effects(&self, atom: Atom) -> Option<bool> {
        self.atom_has_effects_with_traversing(atom, &Visitor::new())
    }

    /// Evaluate an atom with the current mode, performing at least a single
    /// step of normalisation.
    pub fn eval(&self, atom: Atom) -> Result<Atom, NormaliseSignal> {
        match self.potentially_eval(atom)? {
            Some(atom) => Ok(atom),
            None => Ok(atom),
        }
    }

    /// Same as `eval`, but also sets the `evaluated` flag in the given
    /// `EvalState`.
    fn eval_and_record(
        &self,
        atom: Atom,
        state: &NormalisationState,
    ) -> Result<Atom, NormaliseSignal> {
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
    fn eval_fully(&self, atom: Atom) -> Result<Atom, NormaliseSignal> {
        let old_mode = self.mode.replace(NormalisationMode::Full);
        let result = self.eval(atom);
        self.mode.set(old_mode);
        result
    }

    /// Same as `eval_nested`, but with a given evaluation state.
    fn eval_nested_and_record(
        &self,
        atom: Atom,
        state: &NormalisationState,
    ) -> Result<Atom, NormaliseSignal> {
        match self.mode.get() {
            NormalisationMode::Full => self.eval_and_record(atom, state),
            NormalisationMode::Weak => Ok(atom),
        }
    }

    /// Evaluate a block term.
    fn eval_block(&self, block_term: BlockTerm) -> AtomEvaluation {
        self.context().enter_scope(ScopeKind::Stack(block_term.stack_id), || {
            let st = NormalisationState::new();

            for statement in block_term.statements.iter() {
                match *statement.value() {
                    BlockStatement::Decl(mut decl_term) => {
                        decl_term.value = decl_term
                            .value
                            .map(|v| -> Result<_, NormaliseSignal> {
                                Ok(self.to_term(self.eval_nested_and_record(v.into(), &st)?))
                            })
                            .transpose()?;

                        match decl_term.value {
                            Some(value) => match self.match_value_and_get_binds(
                                value,
                                decl_term.bind_pat,
                                &mut |name, term_id| {
                                    self.context().add_untyped_assignment(name, term_id)
                                },
                            )? {
                                MatchResult::Successful => {
                                    // All good
                                }
                                MatchResult::Failed => {
                                    panic!("Non-exhaustive let-binding: {}", decl_term)
                                }
                                MatchResult::Stuck => {
                                    info!("Stuck evaluating let-binding: {}", decl_term);
                                }
                            },
                            None => {
                                panic!("Let binding with no value: {}", decl_term)
                            }
                        }
                    }
                    BlockStatement::Expr(expr) => {
                        let _ = self.eval_and_record(expr.into(), &st)?;
                    }
                }
            }

            let sub = self.sub_ops().create_sub_from_current_scope();
            let result_term = self.eval_and_record(block_term.expr.into(), &st)?;
            let subbed_result_term = self.sub_ops().apply_sub(result_term, &sub);

            normalised_to(subbed_result_term)
        })
    }

    /// Evaluate a variable.
    fn eval_var(&self, var: SymbolId, original_term_id: TermId) -> AtomEvaluation {
        let term_id = Visitor::new().copy(original_term_id);
        let result =
            self.checker().normalise(&mut Context::new(), &mut VarTerm { symbol: var }, term_id)?;
        match result {
            Some(()) => normalised_to(term_id),
            None => Ok(None),
        }
    }

    /// Evaluate a cast term.
    fn eval_cast(&self, cast_term: CastTerm) -> AtomEvaluation {
        // @@Todo: will not play well with typeof?;
        normalised_option(self.potentially_eval(cast_term.subject_term.into())?)
    }

    /// Evaluate a dereference term.
    fn eval_deref(&self, mut deref_term: Node<DerefTerm>) -> AtomEvaluation {
        let st = NormalisationState::new();
        deref_term.subject = self.to_term(self.eval_and_record(deref_term.subject.into(), &st)?);

        // Reduce:
        if let Term::Ref(ref_expr) = *deref_term.subject.value() {
            // Should never be effectful
            return normalised_to(ref_expr.subject);
        }

        normalised_if(|| Term::from(*deref_term, deref_term.origin.computed()), &st)
    }

    /// Get the parameter at the given index in the given argument list.
    fn get_param_in_args(&self, args: ArgsId, target: ParamIndex) -> Atom {
        for arg_i in args.iter() {
            let arg = arg_i.value();
            if arg.target == target || ParamIndex::Position(arg_i.1) == target {
                return arg.value.into();
            }
        }
        panic!("Out of bounds index for access: {}", target)
    }

    /// Set the parameter at the given index in the given argument list.
    fn set_param_in_args(&self, args: ArgsId, target: ParamIndex, value: Atom) {
        let value = self.to_term(value);
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
    fn get_index_in_array(&self, elements: TermListId, index: TermId) -> Option<Atom> {
        try_use_term_as_integer_lit::<_, usize>(self.env, index)
            .map(|idx| elements.elements().at(idx).unwrap().into())
    }

    /// Get the term at the given index in the given repeated array. If the
    /// index term is larger than the `repeat` count, we fail, otherwise
    /// return the `subject`.
    ///
    /// Assumes that the index is normalised.
    fn get_index_in_repeat(&self, subject: TermId, repeat: TermId, index: TermId) -> Option<Atom> {
        let subject = try_use_term_as_integer_lit::<_, usize>(self.env, subject)?;
        let index = try_use_term_as_integer_lit::<_, usize>(self.env, index)?;

        if index >= subject {
            None
        } else {
            Some(repeat.into())
        }
    }

    /// Evaluate an access term.
    fn eval_access(&self, mut access_term: AccessTerm) -> AtomEvaluation {
        let st = NormalisationState::new();
        access_term.subject = self.to_term(self.eval_and_record(access_term.subject.into(), &st)?);

        let result = match *access_term.subject.value() {
            Term::Tuple(tuple) => self.get_param_in_args(tuple.data, access_term.field),
            Term::Ctor(ctor) => self.get_param_in_args(ctor.ctor_args, access_term.field),
            _ => {
                return stuck_normalising();
            }
        };

        let result = self.eval_and_record(result, &st)?;
        normalised_if(|| result, &st)
    }

    /// Evaluate an index term.
    fn eval_index(&self, mut index_term: IndexTerm) -> AtomEvaluation {
        let st = NormalisationState::new();
        index_term.subject = self.to_term(self.eval_and_record(index_term.subject.into(), &st)?);

        if let Term::Array(array_term) = *index_term.subject.value() {
            let result = match array_term {
                ArrayTerm::Normal(elements) => self.get_index_in_array(elements, index_term.index),
                ArrayTerm::Repeated(subject, count) => {
                    // Evaluate the count, and the index terms to integers:
                    self.get_index_in_repeat(subject, count, index_term.index)
                }
            };

            // Check if we actually got the index when evaluating:
            let Some(index) = result else { return stuck_normalising() };

            let result = self.eval_and_record(index, &st)?;
            normalised_if(|| result, &st)
        } else {
            stuck_normalising()
        }
    }

    /// Evaluate an unsafe term.
    fn eval_unsafe(&self, unsafe_term: UnsafeTerm) -> AtomEvaluation {
        // @@Todo: handle unsafe safety
        normalised_option(self.potentially_eval(unsafe_term.inner.into())?)
    }

    /// Evaluate a `typeof` term.
    fn eval_type_of(&self, type_of_term: TyOfTerm) -> AtomEvaluation {
        // Infer the type of the term:
        match tir_stores().atom_info().try_get_inferred_ty(type_of_term.term) {
            Some(ty) => normalised_to(ty),
            None => {
                // Not evaluated yet
                stuck_normalising()
            }
        }
    }

    /// Evaluate a loop control term.
    fn eval_loop_control(&self, loop_control_term: LoopControlTerm) -> NormaliseSignal {
        match loop_control_term {
            LoopControlTerm::Break => NormaliseSignal::Break,
            LoopControlTerm::Continue => NormaliseSignal::Continue,
        }
    }

    /// Evaluate an assignment term.
    fn eval_assign(&self, mut assign_term: Node<AssignTerm>) -> FullEvaluation<Atom> {
        assign_term.value = self.to_term(self.eval(assign_term.value.into())?);

        match *assign_term.subject.value() {
            Term::Access(mut access_term) => {
                access_term.subject = self.to_term(self.eval(access_term.subject.into())?);
                match *access_term.subject.value() {
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
                self.context().modify_assignment(var.symbol, assign_term.value);
            }
            _ => panic!("Invalid assign {}", &*assign_term),
        }

        full_evaluation_to(Term::unit(assign_term.origin.computed()))
    }

    /// Evaluate a match term.
    fn eval_match(&self, mut match_term: MatchTerm) -> AtomEvaluation {
        let st = NormalisationState::new();
        match_term.subject = self.to_term(self.eval_and_record(match_term.subject.into(), &st)?);

        for case_id in match_term.cases.iter() {
            let case = case_id.value();
            let mut outcome = None;

            self.context().enter_scope(
                case.stack_id.into(),
                || -> Result<(), NormaliseSignal> {
                    match self.match_value_and_get_binds(
                        match_term.subject,
                        case.bind_pat,
                        &mut |name, term_id| self.context().add_untyped_assignment(name, term_id),
                    )? {
                        MatchResult::Successful => {
                            let result = self.eval_and_record(case.value.into(), &st)?;
                            outcome = Some(normalised_to(result));
                        }
                        MatchResult::Failed => {}
                        MatchResult::Stuck => {
                            outcome = Some(stuck_normalising());
                        }
                    }

                    Ok(())
                },
            )?;

            match outcome {
                Some(outcome) => return outcome,
                None => continue,
            }
        }

        panic!("Non-exhaustive match: {}", &match_term)
    }

    /// Evaluate a `return` term.
    fn eval_return(&self, return_term: ReturnTerm) -> Result<!, NormaliseSignal> {
        let normalised = self.eval(return_term.expression.into())?;
        Err(NormaliseSignal::Return(normalised))
    }

    /// Evaluate a `loop` term.
    fn eval_loop(&self, loop_term: Node<LoopTerm>) -> FullEvaluation<Atom> {
        loop {
            match self.eval(loop_term.inner.into()) {
                Ok(_) | Err(NormaliseSignal::Continue) => continue,
                Err(NormaliseSignal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        full_evaluation_to(Term::unit(loop_term.origin.computed()))
    }

    /// Evaluate some arguments
    fn eval_args(&self, args_id: ArgsId) -> NormaliseResult<ArgsId> {
        let args = args_id.value();
        let st = NormalisationState::new();

        let evaluated_arg_data = args
            .value()
            .into_iter()
            .map(|arg| -> Result<_, NormaliseSignal> {
                Ok(Node::at(
                    Arg {
                        target: arg.target,
                        value: self.to_term(self.eval_nested_and_record(arg.value.into(), &st)?),
                    },
                    arg.origin,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;

        normalised_if(
            || Node::create_at(Node::<Arg>::seq(evaluated_arg_data), args_id.origin().computed()),
            &st,
        )
    }

    /// Evaluate a function call.
    fn eval_fn_call(&self, mut fn_call: Node<CallTerm>) -> AtomEvaluation {
        let st = NormalisationState::new();

        fn_call.subject = self.to_term(self.eval_and_record(fn_call.subject.into(), &st)?);
        fn_call.args = st.update_from_result(fn_call.args, self.eval_args(fn_call.args))?;

        let subject = *fn_call.subject.value();

        // Beta-reduce:
        if let Term::Fn(fn_def_id) = subject {
            let fn_def = fn_def_id.value();
            if (fn_def.ty.pure || matches!(self.mode.get(), NormalisationMode::Full))
                && tir_stores().atom_info().try_get_inferred_ty(fn_def_id).is_some()
            {
                return self.context().enter_scope(fn_def_id.into(), || {
                    // Add argument bindings:
                    self.context().add_arg_bindings(fn_def.ty.params, fn_call.args);

                    // Evaluate result:
                    match self.eval(fn_def.body.into()) {
                        Err(NormaliseSignal::Return(result)) | Ok(result) => {
                            // Substitute remaining bindings:
                            let sub = self.sub_ops().create_sub_from_current_scope();
                            let result = self.sub_ops().apply_sub(result, &sub);
                            normalised_to(result)
                        }
                        Err(e) => Err(e),
                    }
                });
            }
        } else if let Term::Intrinsic(intrinsic) = subject {
            return self.context().enter_scope(intrinsic.into(), || {
                let args_as_terms =
                    fn_call.args.elements().borrow().iter().map(|arg| arg.value).collect_vec();

                // Run intrinsic:
                let result: Option<TermId> = intrinsic
                    .call(IntrinsicAbilitiesImpl::new(self.env), &args_as_terms)
                    .map_err(TcError::Intrinsic)?;

                normalised_option::<Atom>(result)
            });
        }

        normalised_if(|| Term::from(*fn_call, fn_call.origin.computed()), &st)
    }

    /// Evaluate an atom, performing at least a single step of normalisation.
    ///
    /// Returns `None` if the atom is already normalised.
    fn potentially_eval(&self, atom: Atom) -> AtomEvaluation {
        let mut traversal = Visitor::new();
        traversal.set_visit_fns_once(false);

        let st = NormalisationState::new();
        let nested = Cell::new(false);
        let result = traversal.try_map(atom, |atom| -> Result<_, NormaliseSignal> {
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
                    st.set_normalised();
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

        normalised_if(|| result, &st)
    }

    /// Evaluate an atom once, for use with `fmap`.
    ///
    /// Invariant: if `self.atom_has_effects(atom)`, then `self.eval_once(atom)
    /// != ctrl_continue()`.
    fn eval_once(&self, atom: Atom, nested: bool) -> NormaliseResult<ControlFlow<Atom>> {
        if nested && self.mode.get() == NormalisationMode::Weak {
            // If we're in weak mode, we don't want to evaluate nested atoms
            return already_normalised();
        }

        match atom {
            Atom::Term(term) => match *term.value() {
                Term::TypeOf(term) => ctrl_map(self.eval_type_of(term)),
                Term::Unsafe(unsafe_expr) => ctrl_map(self.eval_unsafe(unsafe_expr)),
                Term::Match(match_term) => ctrl_map(self.eval_match(match_term)),
                Term::Call(fn_call) => {
                    ctrl_map(self.eval_fn_call(term.origin().with_data(fn_call)))
                }
                Term::Cast(cast_term) => ctrl_map(self.eval_cast(cast_term)),
                Term::Hole(Hole(var)) | Term::Var(VarTerm { symbol: var }) => {
                    ctrl_map(self.eval_var(var, term))
                }
                Term::Deref(deref_term) => {
                    ctrl_map(self.eval_deref(term.origin().with_data(deref_term)))
                }
                Term::Access(access_term) => ctrl_map(self.eval_access(access_term)),
                Term::Index(index_term) => ctrl_map(self.eval_index(index_term)),

                // Introduction forms:
                Term::Ref(_)
                | Term::Intrinsic(_)
                | Term::Fn(_)
                | Term::Lit(_)
                | Term::Array(_)
                | Term::Tuple(_)
                | Term::Ctor(_) => ctrl_continue(),

                // Imperative:
                Term::LoopControl(loop_control) => Err(self.eval_loop_control(loop_control)),
                Term::Assign(assign_term) => {
                    ctrl_map_full(self.eval_assign(term.origin().with_data(assign_term)))
                }
                Term::Return(return_expr) => self.eval_return(return_expr)?,
                Term::Block(block_term) => ctrl_map(self.eval_block(block_term)),
                Term::Loop(loop_term) => {
                    ctrl_map_full(self.eval_loop(term.origin().with_data(loop_term)))
                }
                Ty::FnTy(_) | Ty::TupleTy(_) | Ty::DataTy(_) | Ty::Universe | Ty::RefTy(_) => {
                    ctrl_continue()
                }
            },
            Atom::FnDef(_) => already_normalised(),
            Atom::Pat(_) => ctrl_continue(),
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

                let Some(length) = try_use_term_as_integer_lit::<_, usize>(self.env, term) else {
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
            Atom::FnDef(_) | Atom::Pat(_) => false,
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
    fn match_value_and_get_binds(
        &self,
        term_id: TermId,
        pat_id: PatId,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        let evaluated_id = self.to_term(self.eval(term_id.into())?);
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
