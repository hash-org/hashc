use crate::types::TypeId;
use hash_ast::{ident::Identifier, location::Location};

// @@Todo: add ast node locations to these
#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(Location),
    UsingContinueOutsideLoop(Location),
    UsingReturnOutsideFunction(Location),
    RequiresIrrefutablePattern(Location),
    UnresolvedSymbol(Vec<Identifier>),
    UnresolvedStructField(TypeId, Identifier),
    TryingToNamespaceType(Vec<Identifier>),
    TryingToNamespaceVariable(Vec<Identifier>),
    SymbolIsNotAType(Vec<Identifier>),
    SymbolIsNotAVariable(Vec<Identifier>),
    SymbolIsNotATrait(Vec<Identifier>),
    TypeIsNotStruct(TypeId),
    InvalidPropertyAccess(TypeId, Identifier),
    ExpectingBooleanInCondition { found: TypeId },
    MissingStructField(TypeId, Identifier),
    BoundRequiresStrictlyTypeVars,
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;
