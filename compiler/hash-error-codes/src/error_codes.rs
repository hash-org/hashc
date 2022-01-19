macro_rules! error_codes {
    ($($name:ident = $code:expr,)*) => (
        #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
        #[allow(dead_code)]
        pub enum HashErrorCode {
            $($name, )*
        }

        impl HashErrorCode {
            #[allow(unused)]
            pub fn to_num(&self) -> u32 {
                match self {
                    $(Self::$name => $code, )*
                }
            }
        }
    )
}

error_codes! {
    TypeMismatch = 1,
    UsingBreakOutsideLoop = 2,
    UsingContinueOutsideLoop = 3,
    UsingReturnOutsideFunction = 4,
    RequiresIrrefutablePattern = 5,
    UnresolvedSymbol = 6,
    TryingToNamespaceType = 7,
    TryingToNamespaceVariable = 8,
    SymbolIsNotAType = 9,
    SymbolIsNotAVariable = 10,
    SymbolIsNotATrait = 11,
    TypeIsNotStruct = 12,
    UnresolvedStructField = 13,
    InvalidPropertyAccess = 14,
    ExpectingBooleanInCondition = 15,
    MissingStructField = 16,
    BoundRequiresStrictlyTypeVars = 17,
    ExpectingBindingForTraitImpl = 18,
    TraitDefinitionNotFound = 19,
    TypeAnnotationNotAllowedInTraitImpl = 20,
    TypeArgumentLengthMismatch = 21,
    NoMatchingTraitImplementations = 22,
    FunctionArgumentLengthMismatch = 23,
}
