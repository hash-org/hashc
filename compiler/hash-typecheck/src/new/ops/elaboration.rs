use std::{cell::Cell, collections::VecDeque};

use derive_more::Constructor;
use hash_types::new::{
    environment::env::AccessToEnv,
    holes::{Hole, HoleBinder, HoleBinderKind},
    terms::{Term, TermId},
    tys::TyId,
    utils::common::CommonUtils,
};
use hash_utils::store::CloneStore;

use crate::{
    diagnostics::error::TcResult,
    impl_access_to_tc_env,
    new::{
        environment::tc_env::{AccessToTcEnv, TcEnv},
        primitives::subs::Sub,
    },
};

#[derive(Clone, Debug)]
pub struct UnificationProblem {
    src: TermId,
    target: TermId,
    context: Sub,
}

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

    pub fn get_hole_index(&self, hole: Hole) -> usize {
        self.hole_queue.iter().position(|h| *h == hole).unwrap()
    }

    pub fn get_focused_hole(&self) -> Hole {
        self.hole_queue.front().copied().unwrap()
    }

    pub fn focus_hole(&mut self, hole: Hole) {
        let hole_index = self.get_hole_index(hole);
        let target_hole = self.hole_queue.swap_remove_front(hole_index).unwrap();
        self.hole_queue.push_front(target_hole);
    }

    pub fn unfocus_hole(&mut self) {
        let hole_index = 0;
        let target_hole = self.hole_queue.swap_remove_front(hole_index).unwrap();
        self.hole_queue.push_back(target_hole);
    }

    pub fn clear_holes(&mut self) {
        self.hole_queue.clear();
    }

    pub fn add_hole(&mut self, hole: Hole) {
        self.hole_queue.push_front(hole);
    }

    pub fn next_hole(&self) -> Option<Hole> {
        self.hole_queue.front().copied()
    }

    pub fn remove_hole(&mut self) {
        self.hole_queue.pop_front();
    }

    pub fn get_proof_term(&self) -> TermId {
        self.proof_term.get()
    }

    pub fn set_proof_term(&mut self, term: TermId) {
        self.proof_term.set(term);
    }

    pub fn add_problem(&mut self, problem: UnificationProblem) {
        self.problems.push(problem);
    }

    pub fn get_problems(&self) -> &[UnificationProblem] {
        &self.problems
    }

    pub fn clear_problems(&mut self) {
        self.problems.clear();
    }
}

#[derive(Constructor)]
pub struct ElabOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(ElabOps<'tc>);

impl<'tc> ElabOps<'tc> {
    pub fn new_proof_state(&self, ty: TyId) {
        self.new_term_state(ty);
        self.context().clear_to_constant();
    }

    pub fn new_term_state(&self, ty: TyId) {
        let mut proof_state = self.proof_state().borrow_mut();

        let x = self.new_hole();
        let hole_binder = self.new_hole_binder(x, ty, self.new_term(Term::Hole(x)));
        proof_state.set_proof_term(hole_binder);

        proof_state.clear_holes();
        proof_state.add_hole(x);

        proof_state.clear_problems();
    }

    pub fn add_new_hole_to_queue(&self) {
        let hole = self.new_hole();
        self.proof_state().borrow_mut().add_hole(hole);
    }
}

// Tactics:

impl<'tc> ElabOps<'tc> {
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

    fn apply_tactic_on_type(
        &self,
        _tac: impl Fn(HoleBinder) -> TcResult<TermId>,
        _hole: Hole,
        _current: TyId,
    ) -> TcResult<TyId> {
        todo!()
    }

    fn apply_tactic_on_term(
        &self,
        tac: impl Fn(HoleBinder) -> TcResult<TermId>,
        hole: Hole,
        current: TermId,
    ) -> TcResult<TermId> {
        self.stores().term().map(current, |term| match term {
            Term::HoleBinder(hole_binder) => match (hole_binder.kind, hole_binder.hole == hole) {
                (HoleBinderKind::Hole(_), true) => tac(*hole_binder),
                (HoleBinderKind::Hole(_ty), false) => {
                    // let applied_type = self.apply_tactic_on_type(tac, hole, ty)?;
                    // self.context_ops().enter_scope(ScopeKind::, f)

                    // let new_term = self.new_hole_binder(
                    //     hole,
                    //     applied_type,
                    //     self.apply_tactic_on_term(tac, hole, hole_binder.inner)?,
                    // );

                    // let new_ty = self.apply_tactic_on_term(tac, hole,
                    // hole_binder.ty)(args)?;
                    todo!()
                }
                (HoleBinderKind::Guess(_), true) => todo!(),
                (HoleBinderKind::Guess(_), false) => todo!(),
            },
            Term::Runtime(_) => todo!(),
            Term::Tuple(_) => todo!(),
            Term::Prim(_) => todo!(),
            Term::Ctor(_) => todo!(),
            Term::FnCall(_) => todo!(),
            Term::FnRef(_) => todo!(),
            Term::Block(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Loop(_) => todo!(),
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => todo!(),
            Term::DeclStackMember(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(_) => todo!(),
            Term::Ref(_) => todo!(),
            Term::Deref(_) => todo!(),
            Term::Hole(_) => todo!(),
        })
    }
}
