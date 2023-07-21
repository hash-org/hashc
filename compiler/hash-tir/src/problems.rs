use hash_utils::parking_lot::RwLock;

use crate::context::Context;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum UnifyTask {
    Terms(TermId, TermId),
    Tys(TyId, TyId),
    Params(ParamId, ParamId),
    Args(ArgId, ArgId),
}

#[derive(Clone, Debug)]
pub struct Problem {
    pub task: UnifyTask,
    pub context: Context,
}

#[derive(Clone, Debug, Default)]
pub struct Problems {
    // I got 99 problems each of which depend on the other 98.
    data: RwLock<Vec<Problem>>,
}

impl Problems {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_problem(&self, problem: Problem) {
        self.data.write().push(problem);
    }

    pub fn next_problem(&self) -> Option<Problem> {
        self.data.write().pop()
    }

    pub fn has_problems(&self) -> bool {
        self.data.read().is_empty()
    }
}
