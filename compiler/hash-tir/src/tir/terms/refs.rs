//! Definitions related to reference types and terms.

use std::fmt::Display;

use crate::tir::terms::{TermId, TyId};

// @@Todo: explanations about semantics

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
    pub mutable: bool,
    /// The type being referenced.
    pub ty: TyId,
}

/// A reference term.
#[derive(Debug, Clone, Copy)]
pub struct RefTerm {
    /// The kind of reference.
    pub kind: RefKind,
    /// Whether the reference is mutable.
    pub mutable: bool,
    /// The term being referenced.
    pub subject: TermId,
}

/// A dereference term.
#[derive(Debug, Clone, Copy)]
pub struct DerefTerm {
    /// The term being dereferenced.
    pub subject: TermId,
}

impl Display for RefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RefKind::Rc => write!(f, "&rc "),
            RefKind::Raw => write!(f, "&raw "),
            RefKind::Local => write!(f, "&"),
        }
    }
}

impl Display for RefTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}{}", self.kind, if self.mutable { "mut " } else { "" }, self.ty)
    }
}

impl Display for RefTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}{}", self.kind, if self.mutable { "mut " } else { "" }, self.subject)
    }
}

impl Display for DerefTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.subject)
    }
}
