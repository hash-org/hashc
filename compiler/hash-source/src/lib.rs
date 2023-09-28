//! Hash Compiler source location definitions.
#![feature(path_file_prefix, let_chains, lazy_cell, const_trait_impl, box_patterns)]

pub mod constant;
pub mod entry_point;
pub mod identifier;
pub mod location;

use std::{
    collections::HashMap,
    fmt,
    path::{Path, PathBuf},
};

use hash_utils::{
    index_vec::{define_index_type, index_vec, IndexVec},
    parking_lot::RwLock,
    path::adjust_canonicalisation,
};
use location::{ByteRange, LineRanges, RowColRange, SpannedSource};
use once_cell::sync::{Lazy, OnceCell};

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
    #[inline]
    pub fn is_module(&self) -> bool {
        self._raw >> 31 == 1
    }

    /// Check whether the [SourceId] points to a interactive block.
    #[inline]
    pub fn is_interactive(&self) -> bool {
        self._raw >> 31 == 0
    }

    /// Check whether the [SourceId] points to the prelude.
    #[inline]
    pub fn is_prelude(&self) -> bool {
        self._raw == SOURCE_KIND_MASK
    }

    /// Get the actual value of the [SourceId].
    #[inline]
    fn value(&self) -> u32 {
        // clear the last bit
        self._raw & 0x7fff_ffff
    }

    /// Check the [ModuleKind] of a given [SourceId].
    pub fn module_kind(&self) -> Option<ModuleKind> {
        if self.is_interactive() {
            return None;
        }

        let value = self.value();
        SOURCE_MAP.read().modules.get(value as usize).map(|module| module.kind)
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

#[derive(Debug)]
enum SourceKind {
    Module {
        /// The path of the module.
        path: PathBuf,
    },

    /// An interactive block.
    Interactive,
}

#[derive(Debug)]
pub struct Source {
    /// The id of the [Source].
    id: SourceId,

    /// The contents of the module.
    contents: String,

    /// Line ranges for fast lookups, this is only computed when it is needed.
    line_ranges: OnceCell<LineRanges>,

    /// Canonicalised version of the path.
    canonicalised_path: OnceCell<PathBuf>,

    /// Additional information about the source itself.
    extra: SourceKind,
}

impl Source {
    fn new(id: SourceId, contents: String, extra: SourceKind) -> Self {
        Self {
            id,
            contents,
            line_ranges: OnceCell::new(),
            canonicalised_path: OnceCell::new(),
            extra,
        }
    }

    pub fn is_interactive(&self) -> bool {
        matches!(self.extra, SourceKind::Interactive)
    }

    /// Get the contents of the module as a [SpannedSource].
    pub fn contents(&self) -> SpannedSource<'_> {
        SpannedSource(&self.contents)
    }

    /// Get the contents of the module as a [String].
    pub fn owned_contents(&self) -> String {
        self.contents.clone()
    }

    /// Get a hunk of the source by the specified [ByteRange].
    pub fn hunk(&self, range: ByteRange) -> &str {
        &self.contents[range.start()..(range.end() + 1)]
    }

    pub fn row_cols(&self, range: ByteRange) -> RowColRange {
        self.line_ranges().row_cols(range)
    }

    /// Get the line ranges for this particular module.
    pub fn line_ranges(&self) -> &LineRanges {
        self.line_ranges.get_or_init(|| LineRanges::new_from_str(self.id, &self.contents))
    }

    /// Get the path of the module.
    pub fn path(&self) -> &Path {
        match &self.extra {
            SourceKind::Module { path, .. } => path.as_path(),
            SourceKind::Interactive => Path::new("<interactive>"),
        }
    }

    pub fn canonicalised_path(&self) -> &Path {
        self.canonicalised_path
            .get_or_init(|| match &self.extra {
                SourceKind::Module { path } => adjust_canonicalisation(path),
                SourceKind::Interactive => PathBuf::from("<interactive>"),
            })
            .as_path()
    }

    /// Get the name of the [Source].
    pub fn name(&self) -> &str {
        match &self.extra {
            SourceKind::Module { path, .. } => {
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
            SourceKind::Interactive => "<interactive>",
        }
    }
}

/// Stores all of the relevant source information about a particular module.
#[derive(Debug)]
pub struct Module {
    source: Source,

    /// The kind of the module.
    kind: ModuleKind,
}

impl Module {
    /// Create a new [Module].
    pub fn new(id: SourceId, contents: String, path: PathBuf, kind: ModuleKind) -> Self {
        Self { source: Source::new(id, contents, SourceKind::Module { path }), kind }
    }

    /// Create a dummy [Module] entry, this only used.
    fn empty(id: SourceId, path: PathBuf, kind: ModuleKind) -> Module {
        Self { source: Source::new(id, String::new(), SourceKind::Module { path }), kind }
    }
}

// /// A single entry within the interactive mode, this is used to store the
// /// contents of the interactive block. An [InteractiveBlock] is only part
// /// of the `<interactive>` module, and thus does not imply the same behaviour
// /// or handling as a [Module].
#[derive(Debug)]
pub struct InteractiveBlock {
    source: Source,
}

impl InteractiveBlock {
    /// Create a new [InteractiveBlock].
    pub fn new(id: SourceId, contents: String) -> Self {
        Self { source: Source::new(id, contents, SourceKind::Interactive) }
    }
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
    module_paths: HashMap<PathBuf, ModuleId>,

    ///  A map between [ModuleId] and the actual sources of the module.
    modules: IndexVec<ModuleId, Module>,

    /// A map between [InteractiveId] and the actual sources of the interactive
    /// block.
    interactive_blocks: IndexVec<InteractiveId, InteractiveBlock>,
}

impl SourceMap {
    /// Create a new [SourceMap]
    fn new() -> Self {
        Self {
            module_paths: HashMap::new(),
            modules: index_vec![],
            interactive_blocks: index_vec![],
        }
    }

    fn source(&self, id: SourceId) -> &Source {
        if id.is_interactive() {
            &self.interactive_blocks.get(id.value() as usize).unwrap().source
        } else {
            &self.modules.get(id.value() as usize).unwrap().source
        }
    }

    fn add_interactive_block(&mut self, contents: String) -> SourceId {
        let id = self.interactive_blocks.len() as u32;
        let source = SourceId::new_interactive(id);

        self.interactive_blocks.push(InteractiveBlock::new(source, contents));
        source
    }

    /// Get the entry point that has been registered with the [SourceMap].
    ///
    /// If no entry point has been registered, then the function will panic.
    pub fn entry_point(&self) -> Option<ModuleId> {
        self.modules
            .iter()
            .position(|module| matches!(module.kind, ModuleKind::EntryPoint))
            .map(|index| index.into())
    }
}

static SOURCE_MAP: Lazy<RwLock<SourceMap>> = Lazy::new(|| {
    let map = SourceMap::new();
    RwLock::new(map)
});

pub struct SourceMapUtils;

impl SourceMapUtils {
    /// Reserve a [SourceId] a given module.
    pub fn reserve_module(path: PathBuf, kind: ModuleKind) -> SourceId {
        let mut map = SOURCE_MAP.write();

        let id = ModuleId::from_raw(map.modules.len() as u32);
        let source = id.into();
        map.modules.push(Module::empty(source, path.clone(), kind));

        // Create references for the paths reverse
        map.module_paths.insert(path, id);
        source
    }

    pub fn set_module_source(id: SourceId, contents: String) {
        let mut map = SOURCE_MAP.write();
        let id: ModuleId = id.into();

        // Update the entry in the `module` vector. We don't need to put a
        // path in since that happens when the module is reserved.
        map.modules[id].source.contents = contents;
    }

    /// Add an interactive block to the [SourceMap]
    pub fn add_interactive_block(contents: String) -> SourceId {
        SOURCE_MAP.write().add_interactive_block(contents)
    }

    pub fn entry_point() -> Option<SourceId> {
        SOURCE_MAP.read().entry_point().map(SourceId::from)
    }

    /// Get a [SourceId] by a specific [Path]. The function checks if there
    /// is an entry for the specified `path` yielding a [SourceId].
    ///
    /// **Note**: this function has no effect when calling on `interactive`
    /// sources.
    pub fn id_by_path(path: &Path) -> Option<SourceId> {
        SOURCE_MAP.read().module_paths.get(path).copied().map(SourceId::from)
    }

    pub fn map<T>(id: impl Into<SourceId>, f: impl FnOnce(&Source) -> T) -> T {
        let map = SOURCE_MAP.read();
        f(map.source(id.into()))
    }
}
