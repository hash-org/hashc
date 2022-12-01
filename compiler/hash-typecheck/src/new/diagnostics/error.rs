use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    builder::{Reporter, Reports},
    report::{ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::location::SourceLocation;
use hash_types::new::terms::TermId;

use crate::new::{environment::tc_env::WithTcEnv, ops::common::CommonOps};

#[derive(Clone, Debug)]
pub enum TcError {
    /// A series of errors.
    Compound { errors: Vec<TcError> },
    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },
    /// Traits are not yet supported.
    TraitsNotSupported { trait_location: SourceLocation },
}

pub type TcResult<T> = Result<T, TcError>;

impl<'tc> From<WithTcEnv<'tc, &TcError>> for Reports {
    fn from(ctx: WithTcEnv<'tc, &TcError>) -> Self {
        let mut builder = Reporter::new();
        ctx.add_to_reporter(&mut builder);
        builder.build()
    }
}

impl<'tc> WithTcEnv<'tc, &TcError> {
    fn add_to_reporter(&self, reporter: &mut Reporter) {
        let builder = reporter.add_report();
        builder.with_kind(ReportKind::Error);
        match &self.value {
            TcError::NeedMoreTypeAnnotationsToInfer { term } => {
                builder
                    .with_error_code(HashErrorCode::UnresolvedType)
                    .with_message("cannot infer the type of this term".to_string());

                if let Some(location) = self.tc_env().get_location(term) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")))
                        .add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Help,
                            "consider adding more type annotations to this
                expression",
                        )));
                }
            }
            TcError::Compound { errors } => {
                for error in errors {
                    self.tc_env().with(error).add_to_reporter(reporter);
                }
            }
            TcError::TraitsNotSupported { trait_location } => {
                builder.with_error_code(HashErrorCode::UnsupportedTraits).with_message(
                    "traits are work-in-progress and currently not supported".to_string(),
                );

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        *trait_location,
                        "",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        "traits are not yet supported",
                    )));
            }
        }
    }
}
