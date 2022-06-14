//! Hash compiler source location definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use slotmap::new_key_type;
use std::path::Path;

pub mod identifier;
pub mod location;

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

pub trait SourceMap {
    fn path_by_id(&self, source_id: SourceId) -> &Path;
    fn contents_by_id(&self, source_id: SourceId) -> &str;
}
