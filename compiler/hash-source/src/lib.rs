//! Hash Compiler source location definitions.
use slotmap::new_key_type;
use std::path::Path;

pub mod identifier;
pub mod location;
pub mod string;

new_key_type! {
    pub struct ModuleId;
}

new_key_type! {
    pub struct InteractiveId;
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum SourceId {
    Interactive(InteractiveId),
    Module(ModuleId),
}

impl SourceId {
    /// Check whether the [SourceId] points to a module.
    pub fn is_module(&self) -> bool {
        matches!(self, Self::Module(_))
    }
}

pub trait SourceMap {
    fn path_by_id(&self, source_id: SourceId) -> &Path;
    fn contents_by_id(&self, source_id: SourceId) -> &str;
}
