use crate::{params::ParamsId, terms::TermId};

/// A union type.
#[derive(Debug, Clone, Copy)]
pub struct UnionTy {
    pub variants: ParamsId,
}

/// A union term.
#[derive(Debug, Clone, Copy)]
pub struct UnionTerm {
    /// The original union type
    pub original_ty: UnionTy,
    /// The variant index of the union
    pub index: usize,
    /// The contents of the variant
    pub data: TermId,
}
