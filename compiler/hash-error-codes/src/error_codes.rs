//! Hash Error code definitions.

error_codes! {
    // Semantic errors
    UsingBreakOutsideLoop = 2,
    UsingContinueOutsideLoop = 3,
    UsingReturnOutsideFunction = 4,
    // 5: un-used

    // Name spacing and symbol errors
    UnresolvedSymbol = 6,
    UnsupportedAccess = 8,
    UnsupportedNamespaceAccess = 9,
    UnsupportedPropertyAccess = 10,


    UnresolvedStructField = 15,
    InvalidPropertyAccess = 16,
    ExpectingBooleanInCondition = 17,
    MissingStructField = 18,


    // 20: un-used
    TraitDefinitionNotFound = 21,
    NoMatchingTraitImplementations = 24,

    // Type errors
    TypeMismatch = 1,
    TypeIsNotStruct = 13,
    TypeIsNotEnum = 14,
    TypeAnnotationNotAllowedInTraitImpl = 22,
    TypeArgumentLengthMismatch = 23,
    TypeIsNotTypeFunction = 27,
    ValueCannotBeUsedAsType = 28,

    // Errors in regard to parameter lists
    ParameterLengthMismatch = 25,
    ParameterNameMismatch = 26,
    ParameterInUse = 29,
    AmbiguousFieldOrder = 30,
}
