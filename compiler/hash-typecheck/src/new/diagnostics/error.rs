use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_types::new::terms::TermId;

use crate::new::{environment::tc_env::WithTcEnv, ops::common::CommonOps};

pub enum TcError {
    /// @@Todo: write out error variants
    Err,
    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },
}

pub type TcResult<T> = Result<T, TcError>;

impl<'tc> From<WithTcEnv<'tc, TcError>> for Report {
    fn from(ctx: WithTcEnv<'tc, TcError>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error);

        match ctx.value {
            TcError::Err => {
                builder.with_message("Unknown typechecking error");
            }
            TcError::NeedMoreTypeAnnotationsToInfer { term } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedType)
                    .with_message("cannot infer the type of this term".to_string());

                if let Some(location) = ctx.tc_env().get_location(term) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")))
                        .add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Help,
                            "consider adding more type annotations to this
                expression",
                        )));
                }
            }
        }

        builder.build()
    }
}
