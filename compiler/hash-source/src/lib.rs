//! Hash Compiler source location definitions.
#![feature(path_file_prefix, let_chains)]

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use bimap::BiMap;
use hash_utils::path::adjust_canonicalisation;
use index_vec::{define_index_type, index_vec, IndexVec};
use location::{compute_row_col_from_offset, RowColSpan, SourceLocation};

pub mod constant;
pub mod identifier;
pub mod location;

define_index_type! {
    pub struct ModuleId = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "module#{}";

    DISPLAY_FORMAT="{}";
}

define_index_type! {
    pub struct InteractiveId = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "interactive#{}";

    DISPLAY_FORMAT="{}";
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum SourceId {
    /// An Id pointing to a specific interactive block entry.
    Interactive(InteractiveId),
    /// An Id pointing to a specific module entry.
    Module(ModuleId),
}

impl Default for SourceId {
    /// Creates a [SourceId::Module] with a null key
    fn default() -> Self {
        Self::Module(ModuleId::new(0))
    }
}

impl SourceId {
    /// Check whether the [SourceId] points to a module.
    pub fn is_module(&self) -> bool {
        matches!(self, Self::Module(_))
    }

    /// Check whether the [SourceId] points to a interactive block.
    pub fn is_interactive(&self) -> bool {
        matches!(self, Self::Interactive(_))
    }
}

/// The [ModuleKind] enumeration describes what kind of module this is. If it is
/// a [ModuleKind::Prelude], then certain things are allowed within this module
/// in order to allow for `compiler` magic to interact with the prelude file.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ModuleKind {
    /// Any normal module that is within a workspace, including modules within
    /// the standard library.
    Normal,
    /// The `prelude` module, which allows for various features that are
    /// normally disallowed.
    Prelude,
}

/// This data structure is used to store and organise the sources of the
/// modules and interactive blocks. It separates the contents of the sources
/// from the other data structures due to the need to sometimes only read the
/// sources and not care about other metadata that might be owned in some other
/// way.
#[derive(Debug, Default)]
pub struct SourceMap {
    /// A map between [ModuleId] and [PathBuf]. This is a bi-directional map
    /// and such value and key lookups are available.
    module_paths: BiMap<ModuleId, PathBuf>,
    ///  A map between [ModuleId] and the actual sources of the module.
    module_content_map: IndexVec<ModuleId, String>,
    /// A map between [ModuleId] and the kind of module
    module_kind_map: HashMap<ModuleId, ModuleKind>,
    /// A map between [InteractiveId] and the actual sources of the interactive
    /// block.
    interactive_content_map: IndexVec<InteractiveId, String>,
}

impl SourceMap {
    /// Create a new [SourceMap]
    pub fn new() -> Self {
        Self {
            module_paths: BiMap::new(),
            module_kind_map: HashMap::new(),
            module_content_map: index_vec![],
            interactive_content_map: index_vec![],
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

    /// Get a canonicalised version of a [Path] for a [SourceId]. If it is
    /// interactive, the path is always set as `<interactive>`. The function
    /// automatically converts the value into a string.
    pub fn canonicalised_path_by_id(&self, source_id: SourceId) -> String {
        match source_id {
            SourceId::Interactive(_) => String::from("<interactive>"),
            SourceId::Module(_) => adjust_canonicalisation(self.path_by_id(source_id)),
        }
    }

    /// Get the name of a [SourceId] by extracting the path and further
    /// retrieving the stem of the filename as the name of the module. This
    /// function adheres to the rules of module naming conventions which are
    /// specified within the documentation book.
    pub fn source_name(&self, source_id: SourceId) -> &str {
        let path = self.path_by_id(source_id);

        // for interactive, there is no file and so we just default to using the whole
        // path
        if source_id.is_interactive() {
            path.to_str().unwrap()
        } else {
            let prefix = path.file_prefix().unwrap();

            // deal with `index.hash` case...
            if prefix == "index" {
                if let Some(parent) = path.parent() {
                    // Now we should be at the `parent` direct
                    return parent.file_name().unwrap_or(prefix).to_str().unwrap();
                }
            }

            // If it is a normal filename, then just use the resultant prefix, or default
            // to this if trying to extract the name of the parent fails... for example
            // `/index.hash`
            prefix.to_str().unwrap()
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

    /// Get the [ModuleKind] by [SourceId]. If the `id` is
    /// [SourceId::Interactive], then the resultant [ModuleKind] is [None].
    pub fn module_kind_by_id(&self, source_id: SourceId) -> Option<ModuleKind> {
        match source_id {
            SourceId::Interactive(_) => None,
            SourceId::Module(id) => self.module_kind_map.get(&id).cloned(),
        }
    }

    /// Add a module to the [SourceMap]
    pub fn add_module(&mut self, path: PathBuf, contents: String, kind: ModuleKind) -> ModuleId {
        let id = self.module_content_map.push(contents);

        // Create references for the paths reverse
        self.module_paths.insert(id, path);
        self.module_kind_map.insert(id, kind);
        id
    }

    /// Add an interactive block to the [SourceMap]
    pub fn add_interactive_block(&mut self, contents: String) -> InteractiveId {
        self.interactive_content_map.push(contents)
    }

    /// Function to get a friendly representation of the [SourceLocation] in
    /// terms of row and column positions.
    pub fn get_column_row_span_for(&self, location: SourceLocation) -> RowColSpan {
        let source = self.contents_by_id(location.id);

        let start = compute_row_col_from_offset(location.span.start(), source, true);
        let end = compute_row_col_from_offset(location.span.end(), source, false);

        RowColSpan { start, end }
    }

    /// Pretty print a [SourceLocation] in terms of the filename, row and column
    /// to the provided [Write] instance.
    pub fn fmt_location(&self, location: SourceLocation) -> String {
        let name = self.canonicalised_path_by_id(location.id);
        let span = self.get_column_row_span_for(location);

        format!("{name}:{span}")
    }
}
