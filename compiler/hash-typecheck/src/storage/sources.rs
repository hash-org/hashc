//! Contains structures to keep track of which sources have been typechecked.
use super::primitives::TermId;
use hash_source::SourceId;
use std::collections::HashMap;

/// Contains a record of all the sources which have been typechecked, and maps
/// them to (ModDefId)[crate::storage::primitives::ModDefId]s.
#[derive(Debug, Default)]
pub struct CheckedSources {
    data: HashMap<SourceId, TermId>,
}

impl CheckedSources {
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark a given source as checked, by providing its module term.
    pub fn mark_checked(&mut self, source_id: SourceId, mod_def_term: TermId) {
        self.data.insert(source_id, mod_def_term);
    }

    /// Get the module term of the given source if it has already been checked.
    pub fn get_source_mod_def(&self, source_id: SourceId) -> Option<TermId> {
        self.data.get(&source_id).copied()
    }
}
