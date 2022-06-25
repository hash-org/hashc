//! Contains structures to keep track of modules and information relating to
//! them.
use super::primitives::{ModDef, ModDefId};
use slotmap::SlotMap;

/// Stores module definitions, indexed by [ModDefId]s.
#[derive(Debug, Default)]
pub struct ModDefStore {
    data: SlotMap<ModDefId, ModDef>,
}

impl ModDefStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a module, returning its assigned [ModDefId].
    pub fn create(&mut self, mod_def: ModDef) -> ModDefId {
        self.data.insert(mod_def)
    }

    /// Get a module by [ModDefId].
    ///
    /// If the module is not found, this function will panic. However, this
    /// shouldn't happen because the only way to acquire a module is to use
    /// [Self::create], and modules cannot be deleted.
    pub fn get(&self, mod_def_id: ModDefId) -> &ModDef {
        self.data.get(mod_def_id).unwrap()
    }

    /// Get a module by [ModDefId], mutably.
    ///
    /// If the module is not found, this function will panic.
    pub fn get_mut(&mut self, mod_def_id: ModDefId) -> &mut ModDef {
        self.data.get_mut(mod_def_id).unwrap()
    }
}
