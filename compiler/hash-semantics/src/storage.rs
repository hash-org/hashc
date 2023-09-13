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
}
