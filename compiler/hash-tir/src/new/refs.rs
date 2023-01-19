//! Definitions related to reference types and terms.

use std::fmt::Display;

use super::environment::env::{AccessToEnv, WithEnv};
use crate::new::{terms::TermId, tys::TyId};

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

impl Display for WithEnv<'_, &RefTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.value.kind,
            if self.value.mutable { "mut " } else { "" },
            self.env().with(self.value.ty)
        )
    }
}

impl Display for WithEnv<'_, &RefTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.value.kind,
            if self.value.mutable { "mut " } else { "" },
            self.env().with(self.value.subject)
        )
    }
}

impl Display for WithEnv<'_, &DerefTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.env().with(self.value.subject))
    }
}
