//! Hash Compiler source location definitions.
use bimap::BiMap;
use slotmap::{new_key_type, SlotMap};
use std::path::{Path, PathBuf};

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
    /// An Id pointing to a specific interactive block entry.
    Interactive(InteractiveId),
    /// An Id pointing to a specific module entry.
    Module(ModuleId),
}

impl SourceId {
    /// Check whether the [SourceId] points to a module.
    pub fn is_module(&self) -> bool {
        matches!(self, Self::Module(_))
    }
}

/// This data structure is used to store and organise the sources of the
/// [Module]s and [InteractiveBlock]s. It separates the contents of the sources
/// from the other data structures due to the need to sometimes only read the
/// sources and not care about other metadata that might be owned in some other
/// way.
#[derive(Debug, Default)]
pub struct SourceMap {
    /// A map between [ModuleId] and [PathBuf]. This is a bi-directional map
    /// and such value and key lookups are available.
    module_paths: BiMap<ModuleId, PathBuf>,
    ///  A map between [ModuleId] and the actual sources of the module.
    module_content_map: SlotMap<ModuleId, String>,
    ///  A map between [InteractiveId] and the actual sources of the interactive
    /// block.
    interactive_content_map: SlotMap<InteractiveId, String>,
}

impl SourceMap {
    /// Create a new [SourceMap]
    pub fn new() -> Self {
        Self {
            module_paths: BiMap::new(),
            module_content_map: SlotMap::with_key(),
            interactive_content_map: SlotMap::with_key(),
        }
    }

    /// Get a [Path] by a specific [SourceId]. If it is interactive, the path
    /// is always set as `<interactive>`.
    pub fn path_by_id(&self, source_id: SourceId) -> &Path {
        match source_id {
            SourceId::Interactive(_) => Path::new("<interactive>"),
            SourceId::Module(id) => self.module_paths.get_by_left(&id).unwrap().as_path(),
        }
    }

    /// Get a [ModuleId] by a specific [Path]. The function checks if there
    /// is an entry for the specified `path` yielding a [ModuleId]
    pub fn get_module_id_by_path(&self, path: &Path) -> Option<ModuleId> {
        self.module_paths.get_by_right(path).copied()
    }

    /// Get the raw contents of a module or interactive block by the
    /// specified [SourceId]
    pub fn contents_by_id(&self, source_id: SourceId) -> &str {
        match source_id {
            SourceId::Interactive(id) => self.interactive_content_map.get(id).unwrap(),
            SourceId::Module(id) => self.module_content_map.get(id).unwrap(),
        }
    }

    /// Add a module to the [SourceMap]
    pub fn add_module(&mut self, path: PathBuf, contents: String) -> ModuleId {
        let id = self.module_content_map.insert(contents);

        // Create references for the paths reverse
        self.module_paths.insert(id, path);
        id
    }

    /// Add an interactive block to the [SourceMap]
    pub fn add_interactive_block(&mut self, contents: String) -> InteractiveId {
        self.interactive_content_map.insert(contents)
    }
}
