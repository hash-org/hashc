use crate::types::TypeId;
use hash_ast::{ident::Identifier, location::SourceLocation};

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
    TypeIsNotStruct {
        ty: TypeId,
        location: SourceLocation,
        ty_def_location: Option<SourceLocation>,
    },
    UnresolvedStructField {
        field_name: Identifier,
        location: SourceLocation,
        ty_def_name: Identifier, // @@Maybe make this a symbol?
        ty_def_location: Option<SourceLocation>,
    },
    InvalidPropertyAccess {
        field_name: Identifier,
        location: SourceLocation,
        ty_def_name: Identifier,
        ty_def_location: Option<SourceLocation>,
    },
    ExpectingBooleanInCondition {
        found: TypeId,
        location: SourceLocation,
    },
    MissingStructField {
        field_name: Identifier,
        field_location: SourceLocation,
        ty_def_name: Identifier,
        ty_def_location: Option<SourceLocation>,
    },
    BoundRequiresStrictlyTypeVars,
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;
