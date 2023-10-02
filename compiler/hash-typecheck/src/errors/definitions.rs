use hash_ast::lit::LitParseError;
use hash_reporting::diagnostic::IntoCompound;
use hash_source::location::Span;
use hash_tir::{
    tir::{
        fns::FnDefId, NodeOrigin, ParamError, ParamIndex, ParamsId, PatId, SomeParamsOrArgsId,
        TermId, TyId,
    },
    visitor::Atom,
};
use hash_utils::derive_more::From;

/// A kind of wrong term usage.
#[derive(Clone, Debug)]
pub enum WrongTermKind {
    /// Cannot call a term because it is not a function.
    NotAFunction,
    /// Cannot access members because the term is not a record.
    ///
    /// Records are tuples, single constructor data types.
    NotARecord,
    /// Cannot index because the term is not an array.
    NotAnArray,
    /// Cannot use the given term because it is not of the correct type.
    NotOfType { correct_ty: TyId },
}

/// An error that occurs during typechecking.
#[derive(Clone, Debug, From)]

pub enum TcError {
    /// Blocked, cannot continue. This is used as a signal in the typechecker.
    Blocked(NodeOrigin),

    /// Signal to assert that there are other errors in the diagnostics store.
    Signal,

    /// A series of errors.
    Compound { errors: Vec<TcError> },

    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToInfer { atom: Atom },

    /// More type annotations are needed to infer the type of the given term.
    NeedMoreTypeAnnotationsToUnify { src: Atom, target: Atom },

    /// The given arguments do not match the length of the target parameters.
    WrongArgLength { params_id: ParamsId, args_id: SomeParamsOrArgsId },

    /// The given parameters do not match the length of their annotations.
    WrongParamLength { given_params_id: ParamsId, annotation_params_id: ParamsId },

    /// The two given argument lists cannot be unified due to mismatching
    /// lengths.
    DifferentParamOrArgLengths { a: SomeParamsOrArgsId, b: SomeParamsOrArgsId },

    /// Cannot deref the subject.
    CannotDeref { subject: TermId, actual_subject_ty: TyId },

    /// Types don't match
    MismatchingTypes { expected: TyId, actual: TyId },

    /// Types don't match
    MismatchingArrayLengths { expected_len: TermId, got_len: TermId },

    /// Wrong call kind
    WrongCallKind { site: TermId, expected_implicit: bool, actual_implicit: bool },

    /// Wrong type used somewhere
    WrongTy { term: TermId, inferred_term_ty: TyId, kind: WrongTermKind },

    /// The given property does not exist on the given term.
    PropertyNotFound { term: TermId, term_ty: TyId, property: ParamIndex },

    /// Undecidable equality between terms
    UndecidableEquality { a: TermId, b: TermId },

    /// Undecidable equality between terms
    MismatchingPats { a: PatId, b: PatId },

    /// The given property does not exist on the given term.
    MismatchingFns { a: FnDefId, b: FnDefId },

    /// Invalid range pattern literal
    InvalidRangePatternLiteral { location: Span },

    /// Invalid range pattern literal
    TryingToReferenceLocalsInType { ty: TyId },

    /// Cannot use the given term in a type position.
    CannotUseInTyPos { location: NodeOrigin, inferred_ty: TyId },

    /// An error related to argument/parameter matching.
    #[from]
    ParamMatch(ParamError),

    /// Literal parsing error, occurs when provided literals which are of type
    /// integer, and float could not be parsed into their respective types.
    #[from]
    LitParseError(LitParseError),

    /// An error that occurred in an intrinsic.
    Intrinsic(String),
}

impl IntoCompound for TcError {
    fn into_compound(errors: Vec<Self>) -> Self {
        TcError::Compound { errors }
    }
}

pub type TcResult<T> = Result<T, TcError>;
