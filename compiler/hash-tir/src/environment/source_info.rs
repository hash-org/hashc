use std::cell::Cell;

// @@Docs
use hash_source::SourceId;

#[derive(Debug, Clone)]
pub struct CurrentSourceInfo {
    pub source_id: Cell<SourceId>,
}

impl CurrentSourceInfo {
    pub fn new(source_id: SourceId) -> Self {
        Self { source_id: Cell::new(source_id) }
    }

    pub fn set_source_id(&self, source_id: SourceId) {
        self.source_id.set(source_id);
    }

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

    pub fn source_id(&self) -> SourceId {
        self.source_id.get()
    }
}
