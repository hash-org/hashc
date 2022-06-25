//! Contains structures to keep track of which sources have been typechecked.
use super::primitives::ModDefId;
use hash_source::SourceId;
use std::collections::HashMap;

/// Contains a record of all the sources which have been typechecked, and maps
/// them to [ModDefId]s.
#[derive(Debug, Default)]
pub struct CheckedSources {
    data: HashMap<SourceId, ModDefId>,
}

impl CheckedSources {
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark a given source as checked, by providing its module type.
    pub fn mark_checked(&mut self, source_id: SourceId, mod_def_id: ModDefId) {
        self.data.insert(source_id, mod_def_id);
    }

    /// Get the module type of the given source if it has already been checked.
    pub fn source_type_id(&self, source_id: SourceId) -> Option<ModDefId> {
        self.data.get(&source_id).copied()
    }
}
