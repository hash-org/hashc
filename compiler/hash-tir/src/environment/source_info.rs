//! Information about the current source being analysed.
use std::cell::Cell;

use hash_source::SourceId;

/// Stores the source ID of the current source being analysed.
#[derive(Debug, Clone)]
pub struct CurrentSourceInfo {
    pub source_id: Cell<SourceId>,
}

impl CurrentSourceInfo {
    pub fn new(source_id: SourceId) -> Self {
        Self { source_id: Cell::new(source_id) }
    }

    /// Set the current source id.
    pub fn set_source_id(&self, source_id: SourceId) {
        self.source_id.set(source_id);
    }

    /// Execute the given function with the given source id.
    pub fn with_source_id<F, R>(&self, source_id: SourceId, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let old_source_id = self.source_id.get();
        self.source_id.set(source_id);
        let result = f();
        self.source_id.set(old_source_id);
        result
    }

    /// Get the current source id.
    pub fn source_id(&self) -> SourceId {
        self.source_id.get()
    }
}
