use hash_reporting::reporter::{Reporter, Reports};

use crate::environment::sem_env::WithSemEnv;

#[derive(Clone, Debug)]
pub enum SemanticWarning {}

impl<'tc> From<WithSemEnv<'tc, &SemanticWarning>> for Reports {
    fn from(_ctx: WithSemEnv<'tc, &SemanticWarning>) -> Self {
        Reporter::new().into_reports()
    }
}
