//! Error-related data structures for errors that occur during typechecking.
use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_source::location::Span;
use hash_tir::tir::{SymbolId, TermId};
use hash_typecheck::errors::TcError;
use hash_utils::thin_vec::ThinVec;

use crate::passes::resolution::scoping::ContextKind;

pub type SemanticResult<T> = Result<T, SemanticError>;

/// An error that occurs during semantic analysis.
#[derive(Clone, Debug)]
pub enum SemanticError {
    /// A series of errors.
    Compound { errors: ThinVec<SemanticError> },

    /// An error exists, this is just a signal to stop typechecking.
    Signal,

    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { term: TermId },

    /// Traits are not yet supported.
    TraitsNotSupported { trait_location: Span },

    /// Merge declarations are not yet supported.
    MergeDeclarationsNotSupported { merge_location: Span },

    /// Module patterns are not yet supported.
    ModulePatternsNotSupported { location: Span },

    /// Some specified symbol was not found.
    SymbolNotFound { symbol: SymbolId, location: Span, looking_in: ContextKind },

    /// Cannot use a module in a value position.
    CannotUseModuleInValuePosition { location: Span },

    /// Cannot use a module in a type position.
    CannotUseModuleInTypePosition { location: Span },

    /// Cannot use a module in a pattern position.
    CannotUseModuleInPatternPosition { location: Span },

    /// Cannot use a data type in a value position.
    CannotUseDataTypeInValuePosition { location: Span },

    /// Cannot use a data type in a pattern position.
    CannotUseDataTypeInPatternPosition { location: Span },

    /// Cannot use a constructor in a type position.
    CannotUseConstructorInTypePosition { location: Span },

    /// Cannot use a function in type position.
    CannotUseFunctionInTypePosition { location: Span },

    /// Cannot use a function in a pattern position.
    CannotUseFunctionInPatternPosition { location: Span },

    /// Cannot use an intrinsic in a pattern position.
    CannotUseIntrinsicInPatternPosition { location: Span },

    /// Cannot use a non-constant item in constant position.
    CannotUseNonConstantItem { location: Span },

    /// Cannot use the subject as a namespace.
    InvalidNamespaceSubject { location: Span },

    /// Cannot use arguments here.
    UnexpectedArguments { location: Span },

    /// Type error, forwarded from the typechecker.
    TypeError { error: TcError },

    /// Error from exhaustiveness checking.
    ExhaustivenessError { error: ExhaustivenessError },

    /// Type error, forwarded from the typechecker.
    EnumTypeAnnotationMustBeOfDefiningType { location: Span },

    /// Given data definition is not a singleton.
    DataDefIsNotSingleton { location: Span },

    /// An entry point was not found in the entry module.
    EntryPointNotFound,
}

impl From<TcError> for SemanticError {
    fn from(value: TcError) -> Self {
        Self::TypeError { error: value }
    }
}

impl From<ExhaustivenessError> for SemanticError {
    fn from(error: ExhaustivenessError) -> Self {
        Self::ExhaustivenessError { error }
    }
}

/// Warnings that can originate from the semantic analysis phase.
#[derive(Clone, Debug)]
pub enum SemanticWarning {
    /// Compounded warnings.
    Compound { warnings: ThinVec<SemanticWarning> },

    /// A warning that comes from exhaustive pattern checking and
    /// analysis.
    ExhaustivenessWarning { warning: ExhaustivenessWarning },
}

impl From<ExhaustivenessWarning> for SemanticWarning {
    fn from(warning: ExhaustivenessWarning) -> Self {
        Self::ExhaustivenessWarning { warning }
    }
}
