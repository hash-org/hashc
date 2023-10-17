//! Hash Error code definitions.

error_codes! {
    // Semantic errors
    ExpectingBooleanInCondition = 1,
    UsingBreakOutsideLoop = 2,
    UsingContinueOutsideLoop = 3,
    UsingReturnOutsideFn = 4,
    ItemIsImmutable = 5,
    ItemMustBeImmutable = 6,
    MultipleEntryPoints = 7,
    InvalidEntryPointSignature = 8,

    // Name spacing and symbol errors
    UnresolvedSymbol = 10,
    UnsupportedAccess = 11,
    UnsupportedNamespaceAccess = 12,
    UnsupportedPropertyAccess = 13,
    AmbiguousAccess = 14,
    UnresolvedNameInValue = 15,
    InvalidPropertyAccess = 16,
    MissingStructField = 17,
    UninitialisedMember = 18,
    InvalidAssignSubject = 19,

    // Type errors
    TypeMismatch = 20,
    DisallowedType = 21,
    UnresolvedType = 22,
    ValueCannotBeUsedAsType = 24,
    NonRuntimeInstantiable = 25,
    UnsupportedImplicitFnApplication = 26,
    InvalidUnionElement = 28,
    InvalidIndexSubject = 29,
    InvalidCallSubject = 30,

    // Errors in regard to parameters and arguments
    ParameterLengthMismatch = 35,
    ParameterNameMismatch = 36,
    ParameterInUse = 37,
    AmbiguousFieldOrder = 38,

    // traits
    InvalidMergeElement = 50,
    MultipleNominals = 51,
    InvalidPropertyAccessOfNonMethod = 54,

    // Miscellaneous typechecking and semantic errors
    EnumDiscriminantOverflowed = 60,
    DuplicateEnumDiscriminant = 61,

    // Pattern errors
    MismatchingPatBind = 79,
    DuplicateBindInPat = 80,
    MissingPatBind = 81,
    RefutablePat = 82,
    NonExhaustiveMatch = 83,
    InvalidRangePatBoundaries = 84,

    // Lexing/Parsing errors
    InvalidLiteral = 100,
}
