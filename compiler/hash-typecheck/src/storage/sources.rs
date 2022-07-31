//! Contains structures to keep track of which sources have been typechecked.
use super::primitives::TermId;

use hash_source::SourceId;
use std::{cell::Cell, collections::HashMap};

/// Contains a record of all the sources which have been typechecked, and maps
/// them to (ModDefId)[crate::storage::primitives::ModDefId]s.
#[derive(Debug, Default)]
pub struct CheckedSources {
    /// A map between [SourceId] and the module definition.
    ///
    /// No [SourceId::Interactive] entries should exist as this
    /// would be an invariant.
    data: HashMap<SourceId, TermId>,
    /// The id of the current source that is being typechecked.
    ///
    /// Admittedly, this is a bit hacky and should be removed
    /// somehow.
    id: Cell<SourceId>,
}

impl CheckedSources {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the current [SourceId]
    pub fn current_source(&self) -> SourceId {
        self.id.get()
    }

    /// Set the current [SourceId], it does not matter whether
    /// this is a [SourceId::Module] or [SourceId::Interactive]
    pub fn set_current_source(&mut self, id: SourceId) {
        self.id.set(id);
    }

    /// Mark a given source as checked, by providing its module term.
    pub fn mark_checked(&mut self, source_id: SourceId, mod_def_term: TermId) {
        self.data.insert(source_id, mod_def_term);
    }

    /// Get the module term of the given source if it has already been checked.
    pub fn source_mod_def(&self, source_id: SourceId) -> Option<TermId> {
        self.data.get(&source_id).copied()
    }
}
