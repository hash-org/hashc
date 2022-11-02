//! Definitions related to type casting and coercion.
use super::{terms::TermId, tys::TyId};

/// A coercion of a term from one type to another.
///
/// This must be a valid coercion.
#[derive(Debug, Clone, Copy)]
pub struct CoerceTerm {
    pub source_ty: TyId,
    pub target_ty: TyId,
    pub subject: TermId,
}

/// Cast a given term to a given type.
#[derive(Debug, Clone, Copy)]
pub struct CastTerm {
    pub ty: TyId,
    pub subject: TermId,
}
