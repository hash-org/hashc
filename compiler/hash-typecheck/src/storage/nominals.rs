//! Contains structures to keep track of nominal type definitions and
//! information relating to them.
use slotmap::SlotMap;

use super::primitives::{NominalDef, NominalDefId};

/// Stores nominal type definitions, indexed by [NominalDefId]s.
#[derive(Debug, Default)]
pub struct NominalDefStore {
    data: SlotMap<NominalDefId, NominalDef>,
}

impl NominalDefStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a nominal type definition, returning its assigned [NominalDefId].
    pub fn create(&mut self, nominal_def: NominalDef) -> NominalDefId {
        self.data.insert(nominal_def)
    }

    /// Get a nominal type definition by [NominalDefId].
    ///
    /// If the nominal type definition is not found, this function will panic.
    /// However, this shouldn't happen because the only way to acquire a
    /// nominal type definition is to use [Self::create], and nominal type
    /// definitions cannot be deleted.
    pub fn get(&self, nominal_def_id: NominalDefId) -> &NominalDef {
        self.data.get(nominal_def_id).unwrap()
    }

    /// Get a nominal type definition by [NominalDefId], mutably.
    ///
    /// If the nominal type definition is not found, this function will panic.
    pub fn get_mut(&mut self, nominal_def_id: NominalDefId) -> &mut NominalDef {
        self.data.get_mut(nominal_def_id).unwrap()
    }
}
