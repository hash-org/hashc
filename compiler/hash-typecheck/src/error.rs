use std::iter;

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

impl Symbol {
    /// Function to get the identifier path/symbol from the entire [Symbol]
    pub fn get_ident(&self) -> Vec<Identifier> {
        match self {
            Symbol::Compound { path, .. } => path.to_vec(),
            Symbol::Single { symbol, .. } => vec![*symbol],
        }
    }

    pub fn location(&self) -> Option<SourceLocation> {
        match self {
            Symbol::Compound { location, .. } | Symbol::Single { location, .. } => *location,
        }
    }
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
