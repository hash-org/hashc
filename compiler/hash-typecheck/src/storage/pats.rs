//! Contains structures to keep track of patterns and information relating to
//! them.
use super::primitives::{Pat, PatArgs, PatArgsId};
use hash_utils::{new_store, new_store_key};
use slotmap::SlotMap;

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

/// Stores pattern parameters, indexed by [PatArgsId]s.
#[derive(Debug, Default)]
pub struct PatArgsStore {
    data: SlotMap<PatArgsId, PatArgs>,
}

impl PatArgsStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create pattern parameters, returning its assigned [PatArgsId].
    pub fn create(&mut self, params: PatArgs) -> PatArgsId {
        self.data.insert(params)
    }

    /// Get pattern parameters by [PatArgsId].
    pub fn get(&self, id: PatArgsId) -> &PatArgs {
        self.data.get(id).unwrap()
    }

    /// Get pattern parameters by [PatArgsId], mutably.
    pub fn get_mut(&mut self, id: PatArgsId) -> &mut PatArgs {
        self.data.get_mut(id).unwrap()
    }
}
