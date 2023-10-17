//! Definitions related to type casting and coercion.
use core::fmt;

use crate::tir::{TermId, TyId};

/// Annotate a term with a type. See [`CastKind`].
#[derive(Debug, Clone, Copy)]
pub struct AnnotTerm {
    /// The target type to use `subject_term` as.
    pub target_ty: TyId,
    /// The source term to annotate.
    pub subject_term: TermId,
}

impl fmt::Display for AnnotTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} as {})", self.subject_term, self.target_ty)
    }
}
