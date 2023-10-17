//! Error-related data structures for errors that occur during typechecking.
use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_source::location::Span;
use hash_target::discriminant::Discriminant;
use hash_tir::tir::{SymbolId, TermId};
use hash_typecheck::diagnostics::TcError;
use hash_utils::thin_vec::ThinVec;

use crate::passes::resolution::{pat_binds::Bind, scoping::ContextKind};

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

    /// Enum discriminant annotation overflowed for the specifying
    /// type, e.g.
    /// ```
    /// #[repr("u8")]
    /// Foo := enum(
    ///     #[discriminant(256)]
    ///     A
    /// )
    /// ```
    EnumDiscriminantOverflow {
        /// The location of the variant/variant discriminant assignment that
        /// overflowed.
        location: Span,

        /// The location of a discriminant type annotation (if it was specified)
        /// which caused the overflow.
        annotation_origin: Option<Span>,

        /// The discriminant, computed or specified.
        discriminant: Discriminant,
    },

    /// When an explicit discriminant annotation on an enum is used
    /// more than once implicitly or explicitly, e.g.
    /// ```
    /// Foo := enum(
    ///    #[discriminant(1)]
    ///    A,
    ///    #[discriminant(1)]
    ///    B,
    /// )
    /// ```
    DuplicateEnumDiscriminant {
        /// The original location of where the discriminant was assigned, if the
        /// assignment is implicit, then it is the span of the variant.
        original: Span,

        // The location of the duplicate assignment.
        offending: Span,

        // The value that was duplicated.
        value: Discriminant,
    },

    /// Given data definition is not a singleton.
    DataDefIsNotSingleton { location: Span },

    /// An entry point was not found in the entry module.
    EntryPointNotFound,

    /// When a bind within a pattern is duplicated, e.g.
    /// ```
    /// match (1, 2) {
    ///     (a, a) => {}
    /// }
    /// ```
    DuplicateBindInPat {
        /// The secondary mention of the bind.
        offending: Bind,

        /// The bind that was originally specified
        original: Bind,
    },

    /// Within an `or` pattern, where there is a discrepancy between the
    /// declared bounds within two patterns. For example:
    /// ```
    /// match 2 {
    ///     a | b => {}
    /// }
    /// ```
    MissingPatBind {
        /// The span of the pattern that is missing the bind.
        offending: Span,

        /// The bind that is missing from the alternative.
        missing: Bind,
    },

    /// When an alternative pattern contains bindings that are
    /// declared inconsistently, e.g.
    /// ```
    /// match (1, 2) {
    ///   (mut t, a) | (t, a)
    /// }
    /// ```
    MismatchingPatBind {
        /// The offending binding that is mismatched.
        offending: Bind,

        /// The original binding that was specified in the alternative.
        original: Bind,
    },
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
