use hash_tir_utils::lower::TyCache;

use crate::{prelude::DistinguishedItems, progress::AnalysisProgress};

/// Semantic storage is a collection of information that is
/// produced by semantic analysis and typechecking, which lives on
/// for the later compiler stages to read.
#[derive(Default)]
pub struct SemanticStorage {
    /// Progress of semantic analysis.
    pub progress: AnalysisProgress,

    // Some distinguished items, registered during semantic analysis.
    pub distinguished_items: DistinguishedItems,

    /// The conversion cache between TIR types to Repr types.
    pub repr_ty_cache: TyCache,
}
