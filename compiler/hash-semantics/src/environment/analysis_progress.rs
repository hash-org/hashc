//! Contains information about the extent of the analysis performed on each
//! source.
use std::{cell::RefCell, collections::HashMap};

use hash_source::SourceId;

/// Represents a stage of analysis for a given source module.
///
/// This is needed so that analysis stages are idempotent.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnalysisStage {
    None,
    Discovery,
    Resolution,
    HeaderInference,
    BodyInference,
    PreEvaluation,
}

/// Contains information about the extent of the analysis performed on each
/// source.
#[derive(Clone, Debug, Default)]
pub struct AnalysisProgress {
    data: RefCell<HashMap<SourceId, AnalysisStage>>,
}

impl AnalysisProgress {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the analysis stage for the given source.
    pub fn get(&self, source_id: SourceId) -> AnalysisStage {
        self.data.borrow().get(&source_id).copied().unwrap_or(AnalysisStage::None)
    }

    /// Set the analysis stage for the given source.
    pub fn set(&self, source_id: SourceId, stage: AnalysisStage) {
        self.data.borrow_mut().insert(source_id, stage);
    }
}
