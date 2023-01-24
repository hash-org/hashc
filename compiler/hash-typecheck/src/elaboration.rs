//! Contains utilities to perform elaboration with holes.
//!
//! A `ProofState` is kept in typechecking storage, which contains a list of
//! holes which need to be filled, as well as a list of unification problems
//! which need to be solved but can't yet because they contain some
//! non-unifiable holes.
//!
//! This is inspired by the Idris elaborator:
//!
//! Brady, E. C. (2013). Idris, a general-purpose dependently typed programming
//! language: Design and implementation. Journal of Functional Programming, 23,
//! 552–593.
use std::{cell::Cell, collections::VecDeque};

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    environment::context::Context,
    holes::{Hole, HoleBinder},
    terms::{Term, TermId},
    tys::TyId,
    utils::common::CommonUtils,
};

use crate::{errors::TcResult, AccessToTypechecking};

/// Represents a task of unifying a source term with a target term.
///
/// This is done in a certain context, which is stored alongside the problem,
/// though in a boxed form to keep the size of the struct reasonable.
// @@Performance: store the context in a more compact form here.
#[derive(Clone, Debug)]
pub struct UnificationProblem {
    pub src: TermId,
    pub target: TermId,
    pub context: Box<Context>,
}

/// The current elaboration state, which contains the current proof term that is
/// being tackled, a queue of holes to be filled, as well as a set of problems
/// to solve.
#[derive(Clone, Debug)]
pub struct ProofState {
    proof_term: Cell<TermId>,
    hole_queue: VecDeque<Hole>,
    problems: Vec<UnificationProblem>,
}

impl ProofState {
    pub fn new(proof_term: TermId) -> Self {
        Self {
            proof_term: Cell::new(proof_term),
            hole_queue: VecDeque::new(),
            problems: Vec::new(),
        }
    }

    /// Get the index of a hole in the hole queue.
    pub fn get_hole_index(&self, hole: Hole) -> usize {
        self.hole_queue.iter().position(|h| *h == hole).unwrap()
    }

    /// Get the current hole that is being focused on.
    pub fn get_focused_hole(&self) -> Hole {
        self.hole_queue.front().copied().unwrap()
    }

    /// Focus on a hole, moving it to the front of the hole queue.
    pub fn focus_hole(&mut self, hole: Hole) {
        let hole_index = self.get_hole_index(hole);
        let target_hole = self.hole_queue.swap_remove_front(hole_index).unwrap();
        self.hole_queue.push_front(target_hole);
    }

    /// Unfocus on a hole, moving it to the back of the hole queue.
    pub fn unfocus_hole(&mut self) {
        let hole_index = 0;
        let target_hole = self.hole_queue.swap_remove_front(hole_index).unwrap();
        self.hole_queue.push_back(target_hole);
    }

    /// Clear all the holes in the hole queue.
    pub fn clear_holes(&mut self) {
        self.hole_queue.clear();
    }

    /// Add a hole to the front of the hole queue.
    pub fn add_hole(&mut self, hole: Hole) {
        self.hole_queue.push_front(hole);
    }

    /// Get the current hole to be solved in the hole queue.
    pub fn current_hole(&self) -> Option<Hole> {
        self.hole_queue.front().copied()
    }

    /// Remove the current hole from the hole queue.
    pub fn remove_current_hole(&mut self) {
        self.hole_queue.pop_front();
    }

    /// Get the current proof term.
    pub fn get_proof_term(&self) -> TermId {
        self.proof_term.get()
    }

    /// Set the current proof term.
    pub fn set_proof_term(&mut self, term: TermId) {
        self.proof_term.set(term);
    }

    /// Add a new unification problem to the list of problems.
    pub fn add_problem(&mut self, problem: UnificationProblem) {
        self.problems.push(problem);
    }

    /// Get a slice of all the unification problems.
    pub fn get_problems(&self) -> &[UnificationProblem] {
        &self.problems
    }

    /// Clear all the unification problems.
    pub fn clear_problems(&mut self) {
        self.problems.clear();
    }
}

#[derive(Constructor, Deref)]
pub struct ElabOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> ElabOps<'_, T> {
    /// Set up a new proof state for a term of the given type.
    ///
    /// This is the same as `new_term_state`, but also clears the context to
    /// only contain global constants.
    pub fn new_proof_state(&self, ty: TyId) {
        self.new_term_state(ty);
        self.context().clear_to_constant();
    }

    /// Set up a new term state for a term of the given type.
    pub fn new_term_state(&self, ty: TyId) {
        let mut proof_state = self.proof_state().borrow_mut();

        let x = self.new_hole();
        let hole_binder = self.new_hole_binder(x, ty, self.new_term(Term::Hole(x)));
        proof_state.set_proof_term(hole_binder);

        proof_state.clear_holes();
        proof_state.add_hole(x);

        proof_state.clear_problems();
    }

    /// Create and add a new hole to the hole queue.
    pub fn add_new_hole_to_queue(&self) {
        let hole = self.new_hole();
        self.proof_state().borrow_mut().add_hole(hole);
    }

    /// Apply a tactic to the current proof term.
    ///
    /// A tactic is a function that operates on a hole binder term, and resolves
    /// it to some other term. This might be a hole binder itself, or
    /// another term. Tactics are applied recursively to the proof term's inner
    /// terms.
    ///
    /// Most typechecking inference operations are be implemented as tactics.
    pub fn tactic(&self, tac: impl Fn(HoleBinder) -> TcResult<TermId>) -> TcResult<()> {
        let proof_state = self.proof_state().borrow_mut();
        let current_term = proof_state.get_proof_term();
        let focused_hole = proof_state.get_focused_hole();
        drop(proof_state);

        let result = self.apply_tactic_on_term(tac, focused_hole, current_term)?;

        let mut proof_state = self.proof_state().borrow_mut();
        proof_state.set_proof_term(result);
        Ok(())
    }

    // @@Todo:

    pub fn _apply_tactic_on_type(
        &self,
        _tac: impl Fn(HoleBinder) -> TcResult<TermId>,
        _hole: Hole,
        _current: TyId,
    ) -> TcResult<TyId> {
        todo!()
    }

    pub fn apply_tactic_on_term(
        &self,
        _tac: impl Fn(HoleBinder) -> TcResult<TermId>,
        _hole: Hole,
        _current: TermId,
    ) -> TcResult<TermId> {
        todo!()
    }
}
