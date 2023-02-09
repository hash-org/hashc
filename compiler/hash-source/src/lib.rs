//! Hash Compiler source location definitions.
#![feature(path_file_prefix, let_chains, once_cell)]

pub mod attributes;
pub mod constant;
pub mod entry_point;
pub mod identifier;
pub mod location;

use std::{
    fmt,
    path::{Path, PathBuf},
};

use bimap::BiMap;
use hash_utils::{
    index_vec::{define_index_type, index_vec, IndexVec},
    path::adjust_canonicalisation,
};
use location::{compute_row_col_from_offset, RowColSpan, SourceLocation};

/// Used to check what kind of [SourceId] is being
/// stored, i.e. the most significant bit denotes whether
/// it is a module or an interactive block.
const SOURCE_KIND_MASK: u32 = 0x8000_0000;

define_index_type! {
    /// A [ModuleId] is a [SourceId] which points to a module.
    pub struct ModuleId = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "module:{}";
}

define_index_type! {
    /// An [InteractiveId] is a [SourceId] which points to an interactive block.
    pub struct InteractiveId = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "interactive:{}";
}

/// An identifier for a particular source within the compiler
/// workspace. The internal representation of a [SourceId]
/// uses a 4byte identifier which reserves a single bit to
/// denotes whether this points to a "module" or an "interactive"
/// block. Then, it can be used to index any value within the source
/// map.
///
/// The first 31 bits are used to store the actual value of the
/// [SourceId]. The last bit is used to denote whether this is a
/// module or an interactive block.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct SourceId {
    /// The raw value of the identifier.
    _raw: u32,
}

impl fmt::Debug for SourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_module() {
            write!(f, "module:{}", self.value())
        } else {
            write!(f, "interactive:{}", self.value())
        }
    }
}

impl Default for SourceId {
    /// Creates a default [SourceId] which points to the `prelude` module.
    fn default() -> Self {
        Self { _raw: SOURCE_KIND_MASK }
    }
}

impl SourceId {
    /// Create a new "module" [SourceId] from the given value.
    pub fn new_module(id: u32) -> Self {
        // Value cannot be greater than 2^31 - 1
        debug_assert!(id < SOURCE_KIND_MASK);
        Self { _raw: id | SOURCE_KIND_MASK }
    }

    /// Create a new "interactive" [SourceId] from the given value.
    pub fn new_interactive(id: u32) -> Self {
        // Value cannot be greater than 2^31 - 1
        debug_assert!(id < SOURCE_KIND_MASK);
        Self { _raw: id }
    }

    /// Check whether the [SourceId] points to a module.
    pub fn is_module(&self) -> bool {
        self._raw >> 31 == 1
    }

    /// Check whether the [SourceId] points to a interactive block.
    pub fn is_interactive(&self) -> bool {
        self._raw >> 31 == 0
    }

    /// Get the actual value of the [SourceId].
    #[inline]
    fn value(&self) -> u32 {
        // clear the last bit
        self._raw & 0x7fff_ffff
    }
}

impl From<ModuleId> for SourceId {
    fn from(id: ModuleId) -> Self {
        Self::new_module(id.raw())
    }
}

impl From<InteractiveId> for SourceId {
    fn from(id: InteractiveId) -> Self {
        Self::new_interactive(id.raw())
    }
}

impl From<SourceId> for ModuleId {
    fn from(id: SourceId) -> Self {
        debug_assert!(id.is_module());
        ModuleId::from_raw(id.value())
    }
}

impl From<SourceId> for InteractiveId {
    fn from(id: SourceId) -> Self {
        debug_assert!(id.is_interactive());
        InteractiveId::from_raw(id.value())
    }
}

/// The [ModuleKind] enumeration describes what kind of module this is. If it is
/// a [ModuleKind::Prelude], then certain things are allowed within this module
/// in order to allow for `compiler` magic to interact with the prelude file.
///
/// @@TODO: maybe make this a `bitflags!`?
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ModuleKind {
    /// Any normal module that is within a workspace, including modules within
    /// the standard library.
    Normal,

    /// The `prelude` module, which allows for various features that are
    /// normally disallowed.
    Prelude,

    /// Entry point, this module is considered to be the entry point of the
    /// project, it has the same characteristics as a [`ModuleKind::Normal`]
    /// module, but it is also the entry point of the project.
    EntryPoint,
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
    module_content_map: IndexVec<InteractiveId, String>,

    /// A map between [ModuleId] and the kind of module
    module_kind_map: IndexVec<ModuleId, ModuleKind>,

    /// A map between [InteractiveId] and the actual sources of the interactive
    /// block.
    interactive_content_map: IndexVec<InteractiveId, String>,
}

impl SourceMap {
    /// Create a new [SourceMap]
    pub fn new() -> Self {
        Self {
            module_paths: BiMap::new(),
            module_kind_map: index_vec![],
            module_content_map: index_vec![],
            interactive_content_map: index_vec![],
        }
    }

    /// Get a [Path] by a specific [SourceId]. If it is interactive, the path
    /// is always set as `<interactive>`.
    pub fn source_path(&self, id: SourceId) -> &Path {
        if id.is_interactive() {
            Path::new("<interactive>")
        } else {
            self.module_path(id.into())
        }
    }

    /// Get a [Path] for a specific [ModuleId].
    pub fn module_path(&self, id: ModuleId) -> &Path {
        self.module_paths.get_by_left(&id).unwrap().as_path()
    }

    /// Get a canonicalised version of a [Path] for a [SourceId]. If it is
    /// interactive, the path is always set as `<interactive>`. The function
    /// automatically converts the value into a string.
    pub fn canonicalised_path_by_id(&self, id: SourceId) -> String {
        if id.is_interactive() {
            String::from("<interactive>")
        } else {
            let value = id.into();
            adjust_canonicalisation(self.module_paths.get_by_left(&value).unwrap())
        }
    }

    /// Get the name of a [SourceId] by extracting the path and further
    /// retrieving the stem of the filename as the name of the module. This
    /// function adheres to the rules of module naming conventions which are
    /// specified within the documentation book.
    pub fn source_name(&self, id: SourceId) -> &str {
        let path = self.source_path(id);

        // for interactive, there is no file and so we just default to using the whole
        // path
        if id.is_interactive() {
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
    /// is an entry for the specified `path` yielding a [ModuleId].
    ///
    /// N.B. This never returns a [InteractiveId] value.
    pub fn get_id_by_path(&self, path: &Path) -> Option<SourceId> {
        self.module_paths.get_by_right(path).copied().map(SourceId::from)
    }

    /// Get the raw contents of a module or interactive block by the
    /// specified [SourceId]
    pub fn contents_by_id(&self, source_id: SourceId) -> &str {
        if source_id.is_interactive() {
            self.interactive_content_map.get(source_id.value() as usize).unwrap()
        } else {
            self.module_content_map.get(source_id.value() as usize).unwrap()
        }
    }

    /// Get the [ModuleKind] by [SourceId]. If the `id` is
    /// [InteractiveId], then the resultant [ModuleKind] is [None].
    pub fn module_kind_by_id(&self, source_id: SourceId) -> Option<ModuleKind> {
        if source_id.is_interactive() {
            return None;
        }

        let value = source_id.value();
        self.module_kind_map.get(value as usize).copied()
    }

    /// Get the entry point that has been registered with the [SourceMap].
    ///
    /// If no entry point has been registered, then the function will panic.
    pub fn entry_point(&self) -> Option<ModuleId> {
        self.module_kind_map
            .iter()
            .position(|kind| matches!(kind, ModuleKind::EntryPoint))
            .map(|index| index.into())
    }

    /// Add a module to the [SourceMap] with the specified resolved file path,
    /// contents and a kind of module.
    pub fn add_module(&mut self, path: PathBuf, contents: String, kind: ModuleKind) -> SourceId {
        let id = self.module_content_map.len() as u32;
        self.module_content_map.push(contents);

        // Create references for the paths reverse
        let id = ModuleId::from_raw(id);
        self.module_paths.insert(id, path);
        self.module_kind_map.push(kind);
        id.into()
    }

    /// Add an interactive block to the [SourceMap]
    pub fn add_interactive_block(&mut self, contents: String) -> SourceId {
        let id = self.interactive_content_map.len() as u32;
        self.interactive_content_map.push(contents);
        SourceId::new_interactive(id)
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
