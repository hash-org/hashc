//! Hash Compiler pipeline [Workspace]. The [Workspace] data structure
//! is used to group the [SourceMap] and [NodeMap] in the current compilation
//! stage. This is because the two data structures have inter-dependencies in
//! the logic. For example, the [NodeMap] needs to know the [ModuleId] of any
//! given [ModuleEntry]. This can only be known by the [SourceMap] which stores
//! all of the relevant [SourceId]s and their corresponding sources.

use core::fmt;
use std::{collections::HashSet, path::PathBuf};

use derive_more::Constructor;
use hash_ast::{
    ast::OwnsAstNode,
    node_map::{InteractiveBlock, NodeMap},
};
use hash_ast_utils::dump::{AstDump, AstDumpMode};
use hash_source::{ModuleId, ModuleKind, SourceId, SourceMapUtils};
use hash_target::HasTarget;
use hash_utils::{
    bitflags::bitflags,
    fxhash::{FxHashMap, FxHashSet},
    log,
    tree_writing::CharacterSet,
};

use crate::{
    error::PipelineError,
    settings::{CompilerSettings, CompilerStageKind},
};

bitflags! {
    /// Defines the flags that can be used to control the compiler pipeline.
    ///
    /// If no flags are defined on [SourceStageInfo], this means that the particular
    /// source has been parsed and has been added to the workspace.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SourceStageInfo: u8 {
        /// If set, the compiler will no perform desugaring on the module.
        const DESUGARED = 0b00000001;

        /// If set, the compiler will not perform ast expansion on the module.
        const EXPANDED  = 0b00000010;

        /// If set, the compiler will not perform semantic analysis on the module.
        const CHECKED_SEMANTICS  = 0b00000100;

        /// If set, the compiler will not perform type checking on the module.
        const TYPECHECKED = 0b00001000;

        /// If set, the compiler will not perform lowering on the module.
        const LOWERED   = 0b00010000;
    }
}

impl SourceStageInfo {
    /// Check if the source has undergone AST desugaring.
    pub fn is_desugared(&self) -> bool {
        self.contains(SourceStageInfo::DESUGARED)
    }

    /// Check if the source has undergone AST expansion.
    pub fn is_expanded(&self) -> bool {
        self.contains(SourceStageInfo::EXPANDED)
    }

    /// Check if the source has been type checked.
    pub fn is_typechecked(&self) -> bool {
        self.contains(SourceStageInfo::TYPECHECKED)
    }

    /// Check if the source has gone through semantic analysis.
    pub fn is_semantics_checked(&self) -> bool {
        self.contains(SourceStageInfo::CHECKED_SEMANTICS)
    }

    /// Returns true if the source has been lowered.
    pub fn is_lowered(&self) -> bool {
        self.contains(SourceStageInfo::LOWERED)
    }

    /// Set the desugaring flag.
    pub fn set_desugared(&mut self) {
        self.insert(SourceStageInfo::DESUGARED);
    }

    /// Set the expansion flag.
    pub fn set_expanded(&mut self) {
        self.insert(SourceStageInfo::EXPANDED);
    }

    /// Set the type checking flag.
    pub fn set_typechecked(&mut self) {
        self.insert(SourceStageInfo::TYPECHECKED);
    }

    /// Set the semantic analysis flag.
    pub fn set_checked_semantics(&mut self) {
        self.insert(SourceStageInfo::CHECKED_SEMANTICS);
    }

    /// Set the lowering flag.
    pub fn set_lowered(&mut self) {
        self.insert(SourceStageInfo::LOWERED);
    }
}

/// A map of [SourceId]s to their corresponding [SourceStageInfo]. This is used
/// to track the current stage of the compiler pipeline for each source.
#[derive(Debug)]
pub struct StageInfo(FxHashMap<SourceId, SourceStageInfo>);

impl StageInfo {
    /// Create a new [StageInfo] with no sources.
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }

    /// Add a new source to the [SourceStageInfo] with the given [SourceId].
    pub fn add(&mut self, source_id: SourceId, stage: SourceStageInfo) {
        self.0.insert(source_id, stage);
    }

    /// Update the [SourceStageInfo] for a particular module.
    pub fn update(
        &mut self,
        source: SourceId,
        info: impl FnOnce(SourceStageInfo) -> SourceStageInfo,
    ) {
        self.0.entry(source).and_modify(|i| *i = info(*i));
    }

    /// Get the [SourceStageInfo] for a particular module.
    pub fn get(&self, source: SourceId) -> SourceStageInfo {
        self.0.get(&source).copied().unwrap_or(SourceStageInfo::empty())
    }

    /// Set a particular flag for all sources.
    pub fn set_all(&mut self, info: SourceStageInfo) {
        for (_, stage) in self.0.iter_mut() {
            *stage |= info;
        }
    }
}

impl Default for StageInfo {
    fn default() -> Self {
        Self::new()
    }
}

/// Data structure representing the current pipeline workflow. The [Workspace]
/// contains produced data and metadata from all the various stages within the
/// compiler. The [Workspace] represents a shared work space for stages to
/// access information about the current job.
pub struct Workspace {
    /// The name of the current workspace.
    pub name: String,

    /// Represents where the workspace compilation results should be
    /// saved to on disk. This is equivalent to specifying the "output"
    /// directory for the compiler.
    ///
    /// Defaults to the working directory of the entry point file and the
    /// "target" directory, e.g. for the file `src/main.hash` the default
    /// output directory would be `src/target`.
    ///
    /// However, this can be configured using the `--output-dir` flag.
    pub output_directory: PathBuf,

    /// A user specified location of where to write the executable to.
    /// If the user has not specified a location, this will be [`None`], and it
    /// will be generated from the "output" directory and other session
    /// information.
    ///
    /// N.B. To compute the executable path, use [`Workspace::executable_path`].
    pub executable_path: Option<PathBuf>,

    /// Dependency map between sources and modules.
    dependencies: FxHashMap<SourceId, FxHashSet<ModuleId>>,

    /// Stores all of the generated AST for modules and nodes.
    pub node_map: NodeMap,

    /// The results from code generation. This does not store the actual
    /// generated code, but rather the metadata required to build the
    /// final executable.
    pub code_map: CodeMap,

    /// Information about which source have undergone which stages
    /// of the compiler pipeline.
    pub source_stage_info: StageInfo,
}

impl Workspace {
    /// Create a new [Workspace], initialising all members to be empty.
    pub fn new(settings: &CompilerSettings) -> Result<Self, PipelineError> {
        let executable_path = settings.codegen_settings().output_path.clone();
        let output_directory = settings.output_directory()?;

        let name = settings
            .try_entry_point()
            .transpose()?
            .map(|f| f.file_stem().unwrap().to_str().unwrap().to_string())
            .unwrap_or_else(|| "main".to_string());

        Ok(Self {
            name,
            output_directory,
            executable_path,
            node_map: NodeMap::new(),
            dependencies: FxHashMap::default(),
            code_map: CodeMap::default(),
            source_stage_info: StageInfo::new(),
        })
    }

    /// Get the path of the executable that the compiler should write the
    /// final binary to. This is workspace dependant, since the executables
    /// might not even be emitted for a workspaces that don't "require"
    /// executables.
    pub fn executable_path(&self, settings: &CompilerSettings) -> PathBuf {
        let target = settings.target();

        self.executable_path.as_ref().map_or_else(
            || {
                // If no executable path was specified, we create one from the
                // output directory and the name of the entry point file.
                let mut path = self.output_directory.clone();
                path.push(&self.name);
                path.set_extension(target.exe_suffix.as_ref());
                path
            },
            |path| path.clone(),
        )
    }

    /// Get an a temporary location for the output of some kind of
    /// resource that is being emitted. This is used by stages that might
    /// write information onto disk into the temporary workspace storage,
    /// and require a temporary location to write to.
    ///
    /// This function will create the specified temporary storage, returning
    /// an error if the creation of the location fails for any reason.
    pub fn temporary_storage(&self, place: impl AsRef<str>) -> Result<PathBuf, PipelineError> {
        let mut path = self.output_directory.clone();
        path.push(place.as_ref());

        // Now try to create the location...
        if !path.exists() || !path.is_dir() {
            std::fs::create_dir_all(&path)
                .map_err(|error| PipelineError::ResourceCreation { path: path.clone(), error })?;
        }

        Ok(path)
    }

    /// Check whether this [Workspace] will yield an executable.
    pub fn yields_executable(&self, settings: &CompilerSettings) -> bool {
        settings.stage >= CompilerStageKind::Build && SourceMapUtils::entry_point().is_some()
    }

    /// Get the bitcode path for a particular [ModuleId]. This does not
    /// imply that the function will return a path that already exists, or has
    /// been "acquired", it is intended to be used to generate a path for a
    /// module that is about to be emitted.
    pub fn module_bitcode_path(&self, module: ModuleId, extension: &'static str) -> PathBuf {
        let mut path = self.output_directory.clone();
        let module_path = SourceMapUtils::map(module, |source| {
            source.path().file_stem().unwrap().to_str().unwrap().to_string()
        });

        path.push("build");
        path.push(format!("{}-{}.{extension}", module_path, module.raw()));
        path
    }

    /// Add a interactive block to the [Workspace] by providing the contents and
    /// the [InteractiveBlock]. Returns the created [InteractiveId] from
    /// adding it to the source map.
    pub fn add_interactive_block(&mut self, input: String) -> SourceId {
        let id = SourceMapUtils::add_interactive_block(input);
        let block = InteractiveBlock::new();

        // Add this source to the node map, and to the stage info
        self.node_map.add_interactive_block(block);
        self.source_stage_info.add(id, SourceStageInfo::empty());

        id
    }

    /// Add a module to the [Workspace] by providing the contents and the
    /// [ModuleEntry]. Returns the created [SourceId] from adding it to the
    /// source map.
    pub fn add_module(&mut self, path: PathBuf, kind: ModuleKind) -> SourceId {
        let id = SourceMapUtils::reserve_module(path, kind);

        // Add this source to the node map, and to the stage info
        // self.node_map.add_module(module);
        self.source_stage_info.add(id, SourceStageInfo::empty());

        id
    }

    /// Add a module dependency specified by a [SourceId] to a specific source
    /// specified by a [SourceId].
    pub fn add_dependency(&mut self, source_id: SourceId, dependency: ModuleId) {
        self.dependencies.entry(source_id).or_default().insert(dependency);
    }

    /// Utility function used by AST-like stages in order to print the
    /// current [NodeMap].
    pub fn print_sources(&self, mode: AstDumpMode, character_set: CharacterSet) {
        // @@Messaging: Provide a format for sending the AST as an output.
        log::info!("{}", WorkspaceAstDump::new(self, mode, character_set));
    }
}

#[derive(Constructor)]
pub struct WorkspaceAstDump<'ast> {
    /// The workspace.
    workspace: &'ast Workspace,

    /// The style in which the AST should be dumped.
    mode: AstDumpMode,

    /// The character set that should be used when dumping
    /// the AST in the `tree` format. It can a number of options such as, but
    /// not limited to [`CharacterSet::Ascii`] or [`CharacterSet::Unicode`].
    character_set: CharacterSet,
}

impl fmt::Display for WorkspaceAstDump<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { workspace, mode, character_set } = self;

        // @@Todo: use the entry_point on the workspace.
        let entry_point = SourceMapUtils::entry_point().unwrap();

        if entry_point.is_interactive() {
            let node =
                workspace.node_map.get_interactive_block(entry_point.into()).node().ast_ref();
            writeln!(f, "{}", AstDump::new(node.into(), *mode, *character_set))?;
        }

        for (_, module) in workspace.node_map.iter_modules() {
            writeln!(f, "{}", AstDump::new(module.node_ref().into(), *mode, *character_set))?;
        }

        Ok(())
    }
}

/// This defines a map for which modules correspond to which generated object
/// files, symbol files, debug information and any libraries that a module has
/// specified as dependencies.
#[derive(Debug, Clone, Default)]
pub struct CodeMap {
    /// The map of modules to their corresponding object files.
    ///
    /// This is updated as the code generation stage is run, and later
    /// it is used by the linker.
    object_map: FxHashMap<ModuleId, PathBuf>,

    /// This is table of module library dependencies that have been specified
    /// by the module via `#foreign` directives.
    ///
    /// @@Todo: we need to store information about the library type here...
    /// static/dynamic, etc.
    library_dependencies: FxHashMap<ModuleId, HashSet<PathBuf>>,
}

impl CodeMap {
    /// Add an object file entry to the [CodeMap] for the specified [ModuleId].
    pub fn add_object_file(&mut self, module: ModuleId, path: PathBuf) {
        self.object_map.insert(module, path);
    }

    /// Add a module library dependency to the [CodeMap] for the specified
    /// [ModuleId].
    pub fn add_library_dependency(&mut self, module: ModuleId, path: PathBuf) {
        self.library_dependencies.entry(module).or_default().insert(path);
    }

    /// Iterate over all of the module objects that have been generated.
    pub fn objects(&self) -> impl Iterator<Item = &PathBuf> {
        self.object_map.values()
    }
}
