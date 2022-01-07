use crate::types::TypeId;
use hash_ast::{
    ident::Identifier,
    location::{Location, SourceLocation},
};

#[derive(Debug)]
pub enum Symbol {
    Compound {
        path: Vec<Identifier>,
        location: Option<SourceLocation>,
    },
    Single {
        symbol: Identifier,
        location: Option<SourceLocation>,
    },
}

// @@Todo: add ast node locations to these
#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(SourceLocation),
    UsingContinueOutsideLoop(SourceLocation),
    UsingReturnOutsideFunction(SourceLocation),
    RequiresIrrefutablePattern(SourceLocation),
    UnresolvedSymbol(Symbol),
    TryingToNamespaceType(Symbol),
    TryingToNamespaceVariable(Symbol),
    UsingVariableInTypePos(Symbol),
    UsingTypeInVariablePos(Symbol),
    TypeIsNotStruct(TypeId),
    UnresolvedStructField {
        struct_type: TypeId,
        field_name: Identifier,
        location: SourceLocation,
    },
    InvalidPropertyAccess {
        struct_type: TypeId,
        struct_defn_location: Option<SourceLocation>,
        field_name: Identifier,
        access_location: SourceLocation,
    },
    ExpectingBooleanInCondition {
        found: TypeId,
        location: Location,
    },
    MissingStructField {
        struct_type: TypeId,
        field_name: Identifier,
        struct_lit_location: SourceLocation,
    },
    BoundRequiresStrictlyTypeVars,
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;
