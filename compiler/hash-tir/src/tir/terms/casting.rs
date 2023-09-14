//! Definitions related to type casting and coercion.
use core::fmt;

use crate::tir::{TermId, TyId};

/// Cast a given term to a given type. See [`CastKind`].
///
/// This might be produced as a result of a unification.
///
/// @@Future: this could be narrowed down to a more restricted set of choices
/// for `target_ty` and source type.
#[derive(Debug, Clone, Copy)]
pub struct CastTerm {
    /// The target type to cast to.
    pub target_ty: TyId,
    /// The source term to cast from.
    pub subject_term: TermId,
}

impl fmt::Display for CastTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} as {})", self.subject_term, self.target_ty)
    }
}
