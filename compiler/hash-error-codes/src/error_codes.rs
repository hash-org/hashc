//! Hash Error code definitions.

error_codes! {
    // Semantic errors
    ExpectingBooleanInCondition = 1,
    UsingBreakOutsideLoop = 2,
    UsingContinueOutsideLoop = 3,
    UsingReturnOutsideFunction = 4,
    // 5: un-used

    // Name spacing and symbol errors
    UnresolvedSymbol = 10,
    UnsupportedAccess = 11,
    UnsupportedNamespaceAccess = 12,
    UnsupportedPropertyAccess = 13,
    AmbiguousAccess = 14,
    UnresolvedStructField = 15,
    InvalidPropertyAccess = 16,
    MissingStructField = 17,

    // Type errors
    TypeMismatch = 20,
    DisallowedType = 21,
    UnresolvedType = 22,
    TypeIsNotTypeFunction = 23,
    ValueCannotBeUsedAsType = 24,
    NonRuntimeInstantiable = 25,
    UnsupportedTypeFunctionApplication = 26,

    // Errors in regard to parameter lists
    ParameterLengthMismatch = 35,
    ParameterNameMismatch = 36,
    ParameterInUse = 37,
    AmbiguousFieldOrder = 38,

    // traits
    InvalidMergeElement = 50,
    MultipleNominals = 51,
    TraitDefinitionNotFound = 52,
    NoMatchingTraitImplementations = 53,
}
