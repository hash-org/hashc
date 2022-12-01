//! Definitions related to type casting and coercion.
use super::{fns::FnDefId, terms::TermId, tys::TyId};

/// The kind of a cast.
///
/// There are two kinds of cast:
/// 1. Type conversion: this is for casts that do not require a change in the
/// runtime representation of the value, i.e. they are proof irrelevant.
///
/// 2. Value conversion: this is for casts that do require a change in the
/// runtime representation of the value. Contains a function that converts from
/// one to the other.
#[derive(Debug, Clone, Copy)]
pub enum CastKind {
    /// The two types have a proof-irrelevant conversion
    TypeConversion,
    /// The two types have a proof-relevant conversion
    ValueConversion(FnDefId),
}

/// A term which has been cast to a different type.
#[derive(Debug, Clone, Copy)]
pub struct CastedTerm {
    /// The kind of cast that occurred.
    pub kind: CastKind,
    // The type that the term was cast to.
    pub target_ty: TyId,
    // The term that was cast.
    pub term: TermId,
}

/// Cast a given term to a given type. See [`CastKind`].
#[derive(Debug, Clone, Copy)]
pub struct CastTerm {
    /// The target type to cast to.
    pub target_ty: TyId,
    /// The source type to cast from.
    pub subject_ty: TyId,
    /// The source term to cast from.
    pub subject_term: TyId,
}
