use hash_reporting::reporter::{Reporter, Reports};

use crate::new::environment::tc_env::WithTcEnv;

#[derive(Clone, Debug)]
pub enum SemanticWarning {}

impl<'tc> From<WithTcEnv<'tc, &SemanticWarning>> for Reports {
    fn from(_ctx: WithTcEnv<'tc, &SemanticWarning>) -> Self {
        Reporter::new().into_reports()
    }
}
