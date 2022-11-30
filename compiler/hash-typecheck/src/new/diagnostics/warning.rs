use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportKind},
};

use crate::new::environment::tc_env::WithTcEnv;

#[derive(Clone, Debug)]
pub enum TcWarning {}

pub type TcResult<T> = Result<T, TcWarning>;

impl<'tc> From<WithTcEnv<'tc, &TcWarning>> for Report {
    fn from(ctx: WithTcEnv<'tc, &TcWarning>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Warning);
        ctx.add_to_builder(&mut builder);
        builder.build()
    }
}

impl<'tc> WithTcEnv<'tc, &TcWarning> {
    pub fn add_to_builder(&self, _builder: &mut ReportBuilder) {
        match *self.value {}
    }
}
