use hash_reporting::reporter::{Reporter, Reports};

use crate::new::environment::tc_env::WithTcEnv;

#[derive(Clone, Debug)]
pub enum TcWarning {}

impl<'tc> From<WithTcEnv<'tc, &TcWarning>> for Reports {
    fn from(_ctx: WithTcEnv<'tc, &TcWarning>) -> Self {
        Reporter::new().into_reports()
    }
}
