//! Module-related containers and utilities.
//
// All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

/// A module identifier which is an index into [Modules].
pub type ModuleIdx = usize;

/// Represents a single module.
pub struct Module<'a> {
    idx: usize,
    modules: &'a Modules,
}

impl Module<'_> {
    /// Get the content (source text) of the module.
    pub fn content(&self) -> &str {
        self.modules.contents[self.idx].as_ref()
    }

    /// Get the filename (full path) of the module.
    pub fn filename(&self) -> &str {
        self.modules.filenames[self.idx].as_ref()
    }
}

/// Represents a set of loaded modules.
pub struct Modules {
    filenames: Vec<String>,
    contents: Vec<String>,
}

impl Modules {
    /// Get the module at the given index.
    pub fn get_module(&self, idx: ModuleIdx) -> Module<'_> {
        Module { idx, modules: self }
    }
}
