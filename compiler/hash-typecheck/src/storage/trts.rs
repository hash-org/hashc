//! Contains structures to keep track of traits and information relating to them.
use super::primitives::{TrtDef, TrtDefId};
use slotmap::SlotMap;

/// Stores trait definitions, indexed by [TrtDefId]s.
#[derive(Debug, Default)]
pub struct TrtDefStore {
    data: SlotMap<TrtDefId, TrtDef>,
}

impl TrtDefStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a trait, returning its assigned [TrtDefId].
    pub fn create(&mut self, trt_def: TrtDef) -> TrtDefId {
        self.data.insert(trt_def)
    }

    /// Get a trait by [TrtDefId].
    ///
    /// If the trait is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a trait is to use [Self::create], and traits cannot be deleted.
    pub fn get(&self, trt_def_id: TrtDefId) -> &TrtDef {
        self.data.get(trt_def_id).unwrap()
    }

    /// Get a trait by [TrtDefId], mutably.
    ///
    /// If the trait is not found, this function will panic.
    pub fn get_mut(&mut self, trt_def_id: TrtDefId) -> &mut TrtDef {
        self.data.get_mut(trt_def_id).unwrap()
    }
}
