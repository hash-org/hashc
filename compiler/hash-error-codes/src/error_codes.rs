//! Hash Error code definitions.

error_codes! {
    TypeMismatch = 1,
    // Semantic errors
    UsingBreakOutsideLoop = 2,
    UsingContinueOutsideLoop = 3,
    UsingReturnOutsideFunction = 4,
    // 5: un-used
    UnresolvedSymbol = 6,
    TryingToNamespaceType = 7,
    TryingToNamespaceVariable = 8,
    SymbolIsNotAType = 9,
    SymbolIsNotAVariable = 10,
    SymbolIsNotATrait = 11,
    SymbolIsNotAEnum = 12,
    TypeIsNotStruct = 13,
    TypeIsNotEnum = 14,
    UnresolvedStructField = 15,
    InvalidPropertyAccess = 16,
    ExpectingBooleanInCondition = 17,
    MissingStructField = 18,
    BoundRequiresStrictlyTypeVars = 19,
    // 20: un-used
    TraitDefinitionNotFound = 21,
    TypeAnnotationNotAllowedInTraitImpl = 22,
    TypeArgumentLengthMismatch = 23,
    NoMatchingTraitImplementations = 24,
    // Errors in regard to parameter lists
    ParameterLengthMismatch = 25,
    ParameterNameMismatch = 26,
}
