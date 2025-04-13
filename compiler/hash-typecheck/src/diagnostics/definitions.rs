//! Definitions for errors and warnings that can occur during typechecking.

use hash_ast_utils::lit::LitParseError;
use hash_reporting::diagnostic::IntoCompound;
use hash_tir::{
    tir::{
        NodeOrigin, ParamError, ParamIndex, ParamsId, PatId, SomeParamsOrArgsId, TermId, TyId,
        fns::FnDefId,
    },
    visitor::Atom,
};
use hash_utils::derive_more::From;

/// Some sort of wrong term usage.
#[derive(Clone, Debug)]
pub enum WrongTermKind {
    /// Cannot call a term because it is not a function.
    NotAFunction,
    /// Cannot access members because the term is not a record.
    ///
    /// Records are tuples and single constructor data types.
    NotARecord,
    /// Cannot index because the term is not an array.
    NotAnArray,
    /// Cannot use the given term because it is not of the correct type.
    NotOfType { correct_ty: TyId },
}

/// The result type to be used for typechecking operations.
pub type TcResult<T> = Result<T, TcError>;

/// An error that occurs during typechecking.
#[derive(Clone, Debug, From)]
pub enum TcError {
    /// Blocked, cannot continue. This is used as a signal in the typechecker.
    ///
    /// @@Remove: this is to be removed once the typechecker can properly
    /// handle unification blocking.
    Blocked(NodeOrigin),

    /// Signal to assert that there are other errors in the diagnostics store.
    Signal,

    /// A series of errors.
    Compound { errors: Vec<TcError> },

    /// More type annotations are needed to infer the type of the given atom.
    NeedMoreTypeAnnotationsToInfer { atom: Atom },

    /// More type annotations are needed to unify the two atoms.
    NeedMoreTypeAnnotationsToUnify { src: Atom, target: Atom },

    /// The given arguments do not match the length of the target parameters.
    WrongArgLength { params_id: ParamsId, args_id: SomeParamsOrArgsId },

    /// The given parameters do not match the length of their annotations.
    WrongParamLength { given_params_id: ParamsId, annotation_params_id: ParamsId },

    /// The two given argument/parameter lists cannot be unified due to
    /// mismatching lengths.
    DifferentParamOrArgLengths { a: SomeParamsOrArgsId, b: SomeParamsOrArgsId },

    /// Cannot dereference the subject as it is not a reference.
    CannotDeref { subject: TermId, actual_subject_ty: TyId },

    /// Types don't match.
    MismatchingTypes { expected: TyId, actual: TyId },

    /// Arrays have mismatching lengths.
    MismatchingArrayLengths { expected_len: TermId, got_len: TermId },

    /// Wrong call kind, i.e. implicit/explicit.
    WrongCallKind { site: TermId, expected_implicit: bool, actual_implicit: bool },

    /// Wrong term kind used somewhere, expected by a core language construct.
    WrongTerm { term: TermId, inferred_term_ty: TyId, kind: WrongTermKind },

    /// The given property does not exist on the given term.
    PropertyNotFound { term: TermId, term_ty: TyId, property: ParamIndex },

    /// Undecidable equality between terms.
    UndecidableEquality { a: TermId, b: TermId },

    /// The two patterns do not match.
    // @@Todo: remove this in favour of a single mismatch variant.
    MismatchingPats { a: PatId, b: PatId },

    /// The two functions do not match.
    // @@Todo: remove this in favour of a single mismatch variant.
    MismatchingFns { a: FnDefId, b: FnDefId },

    /// A type was returned from a block that references some non-substitutable
    /// local variables in the block.
    TryingToReferenceLocalsInType { ty: TyId },

    /// An error related to argument/parameter matching.
    #[from]
    ParamMatch(ParamError),

    /// Literal parsing error, occurs when provided literals which are of type
    /// integer, and float could not be parsed into their respective types.
    #[from]
    LitParseError(LitParseError),

    /// An error that occurred in an intrinsic.
    /// This is a custom error message determined by the intrinsic.
    Intrinsic(String),
}

impl IntoCompound for TcError {
    fn into_compound(errors: Vec<Self>) -> Self {
        TcError::Compound { errors }
    }
}
