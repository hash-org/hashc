//! Contains structures to keep track of patterns and information relating to
//! them.
use super::primitives::{Pat, PatId, PatParams, PatParamsId};
use slotmap::SlotMap;

/// Stores patterns, indexed by [PatId]s.
#[derive(Debug, Default)]
pub struct PatStore {
    data: SlotMap<PatId, Pat>,
}

impl PatStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a pattern, returning its assigned [PatId].
    pub fn create(&mut self, pat: Pat) -> PatId {
        self.data.insert(pat)
    }

    /// Get a pattern by [PatId].
    pub fn get(&self, id: PatId) -> &Pat {
        self.data.get(id).unwrap()
    }

    /// Get a pattern by [PatId], mutably.
    pub fn get_mut(&mut self, id: PatId) -> &mut Pat {
        self.data.get_mut(id).unwrap()
    }
}

/// Stores pattern parameters, indexed by [PatParamsId]s.
#[derive(Debug, Default)]
pub struct PatParamsStore {
    data: SlotMap<PatParamsId, PatParams>,
}

impl PatParamsStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create pattern parameters, returning its assigned [PatParamsId].
    pub fn create(&mut self, params: PatParams) -> PatParamsId {
        self.data.insert(params)
    }

    /// Get pattern parameters by [PatParamsId].
    pub fn get(&self, id: PatParamsId) -> &PatParams {
        self.data.get(id).unwrap()
    }

    /// Get pattern parameters by [PatParamsId], mutably.
    pub fn get_mut(&mut self, id: PatParamsId) -> &mut PatParams {
        self.data.get_mut(id).unwrap()
    }
}
