use std::cell::RefCell;

use hash_tir::{context::Context, tir::terms::TermId, utils::traversing::Atom};

pub struct Problem {
    pub context: Context,
    pub left: Atom,
    pub right: Atom,
}

pub struct ProblemQueue {
    data: RefCell<Vec<Problem>>,
}

impl ProblemQueue {
    pub fn next_problem(&self) -> Option<Problem> {
        self.data.borrow_mut().pop()
    }

    pub fn add_problem(&self, problem: Problem) {
        self.data.borrow_mut().push(problem);
    }
}
