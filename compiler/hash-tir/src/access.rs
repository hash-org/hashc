//! Definitions related to access operations.

use core::fmt;

use hash_ast::ast;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    params::ParamIndex,
    terms::TermId,
};

/// Term to access a nested value.
#[derive(Debug, Clone, Copy)]
pub struct AccessTerm {
    /// The term to access.
    pub subject: TermId,
    /// The target field of the accessing operation.
    pub field: ParamIndex,
}

impl fmt::Display for WithEnv<'_, &AccessTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}.{}",
            self.env().with(self.value.subject),
            // op,
            self.env().with(self.value.field)
        )
    }
}

impl From<ast::PropertyKind> for ParamIndex {
    fn from(kind: ast::PropertyKind) -> Self {
        match kind {
            ast::PropertyKind::NamedField(f) => ParamIndex::Name(f),
            ast::PropertyKind::NumericField(f) => ParamIndex::Position(f),
        }
    }
}
