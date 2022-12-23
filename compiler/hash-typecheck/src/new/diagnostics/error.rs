use hash_error_codes::error_codes::HashErrorCode;
use hash_reporting::{
    self,
    reporter::{Reporter, Reports},
};
use hash_source::location::SourceLocation;
use hash_types::new::{environment::env::AccessToEnv, symbols::Symbol, terms::TermId};

use crate::new::{environment::tc_env::WithTcEnv, ops::common::CommonOps};

#[derive(Clone, Debug)]
pub enum TcError {
    /// A series of errors.
    Compound { errors: Vec<TcError> },
    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },
    /// Traits are not yet supported.
    TraitsNotSupported { trait_location: SourceLocation },
    /// Merge declarations are not yet supported.
    MergeDeclarationsNotSupported { merge_location: SourceLocation },
    /// Some specified symbol was not found.
    SymbolNotFound { symbol: Symbol, location: SourceLocation },
    /// Cannot use a module in a value position.
    CannotUseModuleInValuePosition { location: SourceLocation },
    /// Cannot use a data type in a value position.
    CannotUseDataTypeInValuePosition { location: SourceLocation },
}

pub type TcResult<T> = Result<T, TcError>;

impl<'tc> From<WithTcEnv<'tc, &TcError>> for Reports {
    fn from(ctx: WithTcEnv<'tc, &TcError>) -> Self {
        let mut builder = Reporter::new();
        ctx.add_to_reporter(&mut builder);
        builder.into_reports()
    }
}

impl<'tc> WithTcEnv<'tc, &TcError> {
    fn add_to_reporter(&self, reporter: &mut Reporter) {
        let error = reporter.error();
        match &self.value {
            TcError::NeedMoreTypeAnnotationsToInfer { term } => {
                error
                    .code(HashErrorCode::UnresolvedType)
                    .title("cannot infer the type of this term".to_string());

                if let Some(location) = self.tc_env().get_location(term) {
                    error
                        .add_span(location)
                        .add_help("consider adding more type annotations to this expression");
                }
            }
            TcError::Compound { errors } => {
                for error in errors {
                    self.tc_env().with(error).add_to_reporter(reporter);
                }
            }
            TcError::TraitsNotSupported { trait_location } => {
                error
                    .code(HashErrorCode::UnsupportedTraits)
                    .title("traits are work-in-progress and currently not supported".to_string());

                error.add_span(*trait_location).add_help("cannot use traits yet");
            }
            TcError::MergeDeclarationsNotSupported { merge_location } => {
                error
                    .code(HashErrorCode::UnsupportedTraits)
                    .title("merge declarations are currently not supported".to_string());

                error.add_span(*merge_location).add_help("cannot use merge declarations yet");
            }
            TcError::SymbolNotFound { symbol, location } => {
                error.code(HashErrorCode::UnresolvedSymbol).title(format!(
                    "cannot find name `{}` in the current scope",
                    self.tc_env().env().with(*symbol)
                ));

                error.add_span(*location).add_info("not found in the current scope");
            }
            TcError::CannotUseModuleInValuePosition { location } => {
                error
                    .code(HashErrorCode::UnresolvedSymbol)
                    .title("cannot use a module in expression position");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a module");
            }
            TcError::CannotUseDataTypeInValuePosition { location } => {
                error
                    .code(HashErrorCode::UnresolvedSymbol)
                    .title("cannot use a data type in expression position")
                    .add_help("consider using a constructor call instead");

                error
                    .add_span(*location)
                    .add_info("cannot use this in expression position as it is a data type");
            }
        }
    }
}
