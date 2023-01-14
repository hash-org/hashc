//! Hash Compiler pipeline [Workspace]. The [Workspace] data structure
//! is used to group the [SourceMap] and [NodeMap] in the current compilation
//! stage. This is because the two data structures have inter-dependencies in
//! the logic. For example, the [NodeMap] needs to know the [ModuleId] of any
//! given [ModuleEntry]. This can only be known by the [SourceMap] which stores
//! all of the relevant [SourceId]s and their corresponding sources.

use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use bitflags::bitflags;
use hash_ast::{
    ast::{AstVisitor, OwnsAstNode},
    node_map::{InteractiveBlock, ModuleEntry, NodeMap},
    tree::AstTreeGenerator,
};
use hash_source::{ModuleId, ModuleKind, SourceId, SourceMap};
use hash_utils::tree_writing::TreeWriter;

bitflags! {
    /// Defines the flags that can be used to control the compiler pipeline.
    ///
    /// If no flags are defined on [SourceStageInfo], this means that the particular
    /// source has been parsed and has been added to the workspace.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SourceStageInfo: u32 {
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
pub struct StageInfo(HashMap<SourceId, SourceStageInfo>);

impl StageInfo {
    /// Create a new [StageInfo] with no sources.
    pub fn new() -> Self {
        Self(HashMap::new())
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
#[derive(Debug)]
pub struct Workspace {
    /// Dependency map between sources and modules.
    dependencies: HashMap<SourceId, HashSet<ModuleId>>,

    /// Stores all of the raw file contents of the interactive blocks and
    /// modules.
    pub source_map: SourceMap,

    /// Stores all of the generated AST for modules and nodes
    pub node_map: NodeMap,

    /// Information about which source have undergone which stages
    /// of the compiler pipeline.
    pub source_stage_info: StageInfo,
}

impl Default for Workspace {
    fn default() -> Self {
        Self::new()
    }
}

impl Workspace {
    /// Create a new [Workspace], initialising all members to be empty.
    pub fn new() -> Self {
        Self {
            source_map: SourceMap::new(),
            node_map: NodeMap::new(),
            dependencies: HashMap::new(),
            source_stage_info: StageInfo::new(),
        }
    }

    /// Add a interactive block to the [Workspace] by providing the contents and
    /// the [InteractiveBlock]. Returns the created [InteractiveId] from
    /// adding it to the source map.
    pub fn add_interactive_block(&mut self, input: String, block: InteractiveBlock) -> SourceId {
        let id = self.source_map.add_interactive_block(input);

        // Add this source to the node map, and to the stage info
        self.node_map.add_interactive_block(block);
        self.source_stage_info.add(id, SourceStageInfo::empty());

        id
    }

    /// Add a module to the [Workspace] by providing the contents and the
    /// [ModuleEntry]. Returns the created [SourceId] from adding it to the
    /// source map.
    pub fn add_module(
        &mut self,
        contents: String,
        module: ModuleEntry,
        kind: ModuleKind,
    ) -> SourceId {
        let id = self.source_map.add_module(module.path.to_owned(), contents, kind);

        // Add this source to the node map, and to the stage info
        self.node_map.add_module(module);
        self.source_stage_info.add(id, SourceStageInfo::empty());

        id
    }

    /// Get the [SourceId] of the module by the specified [Path].
    ///
    /// N.B. This function will never return a [SourceId] for an interactive
    /// block.
    pub fn get_id_by_path(&self, path: &Path) -> Option<SourceId> {
        self.source_map.get_id_by_path(path)
    }

    /// Add a module dependency specified by a [SourceId] to a specific source
    /// specified by a [SourceId].
    pub fn add_dependency(&mut self, source_id: SourceId, dependency: ModuleId) {
        self.dependencies.entry(source_id).or_insert_with(HashSet::new).insert(dependency);
    }

    /// Utility function used by AST-like stages in order to print the
    /// current [NodeMap].
    pub fn print_sources(&self, entry_point: SourceId) {
        if entry_point.is_interactive() {
            // If this is an interactive statement, we want to print the statement that was
            // just parsed.
            let source = self.node_map.get_interactive_block(entry_point.into());
            let tree = AstTreeGenerator.visit_body_block(source.node_ref()).unwrap();

            println!("{}", TreeWriter::new(&tree));
        } else {
            // If this is a module, we want to print all of the generated modules from the
            // parsing stage
            for generated_module in self.node_map.iter_modules() {
                let tree = AstTreeGenerator.visit_module(generated_module.node_ref()).unwrap();

                println!(
                    "AST for `{}`:\n{}",
                    generated_module.canonicalised_path(),
                    TreeWriter::new(&tree)
                );
            }
        }
    }
}
