//! Definitions related to access operations.

use core::fmt;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    params::ParamTarget,
    terms::TermId,
};

/// The kind of an access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessKind {
    /// Accessing a constructor field, like `f := Foo(name=3); f.name`.
    CtorField,
    /// Accessing a tuple field, like `f := (2, 3); f.0`.
    TupleField,
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

impl fmt::Display for WithEnv<'_, &AccessTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self.value.kind {
            AccessKind::CtorField => ".",
            AccessKind::TupleField => ".",
        };
        write!(
            f,
            "{}{}{}",
            self.env().with(self.value.subject),
            op,
            self.env().with(self.value.field)
        )
    }
}
