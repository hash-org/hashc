//! Contains structures to keep track of which sources have been typechecked.
use hash_source::SourceId;
use hash_types::terms::TermId;
use hash_utils::store::{DefaultPartialStore, PartialCloneStore, PartialStore};

/// Contains a record of all the sources which have been typechecked, and maps
/// them to (ModDefId)[hash_types::mods::ModDefId]s.
#[derive(Debug, Default)]
pub struct CheckedSources {
    /// A map between [SourceId] and the module definition.
    ///
    /// No [SourceId::Interactive] entries should exist as this
    /// would be an invariant.
    data: DefaultPartialStore<SourceId, TermId>,
}

impl CheckedSources {
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark a given source as checked, by providing its module term.
    pub fn mark_checked(&self, source_id: SourceId, mod_def_term: TermId) {
        self.data.insert(source_id, mod_def_term);
    }

    /// Get the module term of the given source if it has already been checked.
    pub fn source_mod_def(&self, source_id: SourceId) -> Option<TermId> {
        self.data.get(source_id)
    }
}
