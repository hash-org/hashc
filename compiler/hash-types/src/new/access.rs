//! Definitions related to access operations.

use super::{params::ParamTarget, terms::TermId};

/// The kind of an access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessKind {
    /// Accessing a constructor field, like `f := Foo(name=3); f.name`.
    CtorField,
    /// Accessing a tuple field, like `f := (2, 3); f.0`.
    TupleField,
    /// Accessing a module member, like `X := mod { y := 3 }; X.y`.
    ModMember,
    /// Accessing a trait member, like `T := trait { y := 3; z := Self.y }`
    TrtMember,
    /// Accessing a datatype constructor, like `Colour := enum(Red, Green,
    /// Blue); Colour.Red`
    Ctor,
}

/// Term to access a nested value.
#[derive(Debug, Clone, Copy)]
pub struct AccessTerm {
    /// The term to access.
    pub subject: TermId,
    /// The kind of access.
    pub kind: AccessKind,
    /// The target field of the accessing operation.
    pub field: ParamTarget,
}
