//! Contains structures to keep track of patterns and information relating to
//! them.
use super::primitives::{Pattern, PatternId, PatternParams, PatternParamsId};
use slotmap::SlotMap;

/// Stores patterns, indexed by [PatternId]s.
#[derive(Debug, Default)]
pub struct PatternStore {
    data: SlotMap<PatternId, Pattern>,
}

impl PatternStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a pattern, returning its assigned [PatternId].
    pub fn create(&mut self, pattern: Pattern) -> PatternId {
        self.data.insert(pattern)
    }

    /// Get a pattern by [PatternId].
    pub fn get(&self, pattern_id: PatternId) -> &Pattern {
        self.data.get(pattern_id).unwrap()
    }

    /// Get a pattern by [PatternId], mutably.
    pub fn get_mut(&mut self, pattern_id: PatternId) -> &mut Pattern {
        self.data.get_mut(pattern_id).unwrap()
    }
}

/// Stores pattern parameters, indexed by [PatternParamsId]s.
#[derive(Debug, Default)]
pub struct PatternParamsStore {
    data: SlotMap<PatternParamsId, PatternParams>,
}

impl PatternParamsStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create pattern parameters, returning its assigned [PatternParamsId].
    pub fn create(&mut self, pattern_params: PatternParams) -> PatternParamsId {
        self.data.insert(pattern_params)
    }

    /// Get pattern parameters by [PatternParamsId].
    pub fn get(&self, pattern_params_id: PatternParamsId) -> &PatternParams {
        self.data.get(pattern_params_id).unwrap()
    }

    /// Get pattern parameters by [PatternParamsId], mutably.
    pub fn get_mut(&mut self, pattern_params_id: PatternParamsId) -> &mut PatternParams {
        self.data.get_mut(pattern_params_id).unwrap()
    }
}
