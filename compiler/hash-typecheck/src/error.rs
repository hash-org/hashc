use crate::types::TypeId;
use hash_ast::{ident::Identifier, location::Location};

#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(Location),
    UsingContinueOutsideLoop(Location),
    UsingReturnOutsideFunction(Location),
    RequiresIrrefutablePattern(Location),
    UnresolvedSymbol(Vec<Identifier>),
    TryingToNamespaceType(Vec<Identifier>),
    TryingToNamespaceVariable(Vec<Identifier>),
    UsingVariableInTypePos(Vec<Identifier>),
    UsingTypeInVariablePos(Vec<Identifier>),
    InvalidPropertyAccess(TypeId, Identifier),
    ExpectingBooleanInCondition { found: TypeId },
    // @@Todo: turn this into variants
    Message(String),
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;
