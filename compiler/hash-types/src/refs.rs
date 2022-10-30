//! Definitions related to reference types.

use crate::{terms::TermId, types::TyId};

/// The kind of a reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefKind {
    /// A reference-counted reference
    Rc,
    /// A raw reference
    Raw,
    /// A local reference (cannot be stored in structures)
    Local,
}

/// A reference to a type.
#[derive(Debug, Clone, Copy)]
pub struct RefTy {
    /// The kind of reference.
    pub kind: RefKind,
    /// Whether the reference is mutable.
    pub is_mutable: bool,
    /// The type being referenced.
    pub ty: TyId,
}

/// A reference term.
#[derive(Debug, Clone, Copy)]
pub struct RefTerm {
    /// The kind of reference.
    pub kind: RefKind,
    /// Whether the reference is mutable.
    pub is_mutable: bool,
    /// The term being referenced.
    pub subject: TermId,
}

/// A dereference term.
#[derive(Debug, Clone, Copy)]
pub struct DerefTerm {
    /// The term being dereferenced.
    pub subject: TermId,
}
