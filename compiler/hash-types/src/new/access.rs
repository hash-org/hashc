//! Definitions related to access operations.

use super::{symbols::Symbol, terms::TermId};

/// The kind of an access.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AccessKind {
    Numeric(usize),
    Named(Symbol),
}

/// Term to access a nested value.
#[derive(Debug, Clone, Copy)]
pub struct AccessTerm {
    pub subject: TermId,
    pub access_kind: AccessKind,
}
