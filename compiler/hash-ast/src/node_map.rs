//! Defines a data structure that holds all of the nodes that have been parsed.
//! This is used to ensure that the same node is not parsed and to retrieve
//! nodes in later compilation stages.
use std::{
    collections::{
        hash_map::{Iter, IterMut},
        HashMap,
    },
    path::{Path, PathBuf},
};

use hash_source::{InteractiveId, ModuleId, SourceId};
use hash_utils::path::adjust_canonicalisation;

use crate::ast::{AstNode, BodyBlock, Module, OwnsAstNode};

/// Union of a [Source] within [NodeMap]. It can either be a [ModuleEntry]
/// or an [InteractiveBlock].
#[derive(Debug)]
pub enum Source {
    /// If the source is an [InteractiveBlock]
    Interactive(InteractiveBlock),
    /// If the source is an [Module]
    Module(ModuleEntry),
}

/// Data structure which holds information and compiler stage results for a
/// particular interactive block. Currently, this only stores the generated
/// [AstNode<BodyBlock>] from parsing.
#[derive(Debug, Default)]
pub struct InteractiveBlock {
    /// The generated node, only filled in when parsing is complete.
    node: Option<AstNode<BodyBlock>>,
}

impl InteractiveBlock {
    /// Create a new [InteractiveBlock]. Initially sets the `node` as being
    /// [None].
    pub fn new() -> Self {
        Self { node: None }
    }

    /// Set the `node` for given [InteractiveBlock]
    pub fn set_node(&mut self, node: AstNode<BodyBlock>) {
        self.node = Some(node);
    }
}

impl OwnsAstNode<BodyBlock> for InteractiveBlock {
    /// Get a reference to node within [InteractiveBlock]. This
    /// assumes that the node had already been set.
    fn node(&self) -> &AstNode<BodyBlock> {
        self.node.as_ref().unwrap()
    }

    /// Get a mutable reference to node within [InteractiveBlock]. This
    /// assumes that the node had already been set.
    fn node_mut(&mut self) -> &mut AstNode<BodyBlock> {
        self.node.as_mut().unwrap()
    }
}

/// Represents a module that was added to the [NodeMap]. [Module] holds
/// meta data about the module, such as the path. It also holds the
/// parsed [ast::AstNode<ast::Module>] within the data structure. This is
/// set to being optional because it is likely that the generated AST
/// is added later.
#[derive(Debug)]
pub struct ModuleEntry {
    /// The absolute path of the module on disk.
    pub path: PathBuf,
    /// The generated AST for the module, set when parsing is complete.
    node: Option<AstNode<Module>>,
}

impl ModuleEntry {
    /// Create a new [ModuleEntry] with a specified `path` and the `node being
    /// set to [None].
    pub fn new(path: PathBuf) -> Self {
        Self { path, node: None }
    }

    /// Get the `path` from the [Module].
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Get the canonicalised `path` from the [Module].
    pub fn canonicalised_path(&self) -> String {
        adjust_canonicalisation(self.path())
    }

    /// Set the `node` for given [Module]
    pub fn set_node(&mut self, node: AstNode<Module>) {
        self.node = Some(node);
    }
}

impl OwnsAstNode<Module> for ModuleEntry {
    /// Get a reference to node within [ModuleEntry]. This
    /// assumes that the node had already been set.
    fn node(&self) -> &AstNode<Module> {
        self.node.as_ref().unwrap()
    }

    /// Get a mutable reference to node within [ModuleEntry]. This
    /// assumes that the node had already been set.
    fn node_mut(&mut self) -> &mut AstNode<Module> {
        self.node.as_mut().unwrap()
    }
}

/// Wrapper for [Source] in order to get a reference to the
/// enclosed module or interactive block.
#[derive(Debug, Copy, Clone)]
pub enum SourceRef<'i> {
    /// If the source is an [InteractiveBlock]
    Interactive(&'i InteractiveBlock),
    /// If the source is an [ModuleEntry]
    Module(&'i ModuleEntry),
}

/// The [NodeMap] is a data structure that holds all of the nodes that have been
/// parsed within the current [Workspace].
#[derive(Debug, Default)]
pub struct NodeMap {
    /// All [Module] nodes that have been parsed.
    modules: HashMap<ModuleId, ModuleEntry>,
    /// All [InteractiveBlock] nodes that have been parsed.
    interactive_blocks: HashMap<InteractiveId, InteractiveBlock>,
}

impl NodeMap {
    /// Create a new [NodeMap]
    pub fn new() -> Self {
        Self { modules: HashMap::new(), interactive_blocks: HashMap::new() }
    }

    /// Add a [InteractiveBlock] to the [NodeMap]
    pub fn add_interactive_block(&mut self, id: InteractiveId, block: InteractiveBlock) {
        self.interactive_blocks.insert(id, block);
    }

    /// Add a [Module] to the [NodeMap]
    pub fn add_module(&mut self, id: ModuleId, module: ModuleEntry) {
        self.modules.insert(id, module);
    }

    /// Get a [SourceRef] by [SourceId].
    pub fn get_source(&self, source_id: SourceId) -> SourceRef<'_> {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                SourceRef::Interactive(self.get_interactive_block(interactive_id))
            }
            SourceId::Module(module_id) => SourceRef::Module(self.get_module(module_id)),
        }
    }

    /// Get a reference to an [InteractiveBlock], panics if the [InteractiveId]
    /// has no backing [InteractiveBlock].
    pub fn get_interactive_block(&self, interactive_id: InteractiveId) -> &InteractiveBlock {
        self.interactive_blocks.get(&interactive_id).unwrap()
    }

    /// Get a mutable reference to an [InteractiveBlock], panics if the
    /// [InteractiveId] has no backing [InteractiveBlock].
    pub fn get_interactive_block_mut(
        &mut self,
        interactive_id: InteractiveId,
    ) -> &mut InteractiveBlock {
        self.interactive_blocks.get_mut(&interactive_id).unwrap()
    }

    /// Get a mutable reference to an [Module], panics if the [ModuleId]
    /// has no backing [Module].
    pub fn get_module(&self, module_id: ModuleId) -> &ModuleEntry {
        self.modules.get(&module_id).unwrap()
    }

    /// Get a reference to an [Module], panics if the [ModuleId]
    /// has no backing [Module].
    pub fn get_module_mut(&mut self, module_id: ModuleId) -> &mut ModuleEntry {
        self.modules.get_mut(&module_id).unwrap()
    }

    /// /// Create an [Iter] over the currently stores modules within [NodeMap]
    pub fn iter_modules(&self) -> Iter<'_, ModuleId, ModuleEntry> {
        self.modules.iter()
    }

    /// Create an [IterMut] over the currently stores modules within [NodeMap].
    pub fn iter_mut_modules(&mut self) -> IterMut<'_, ModuleId, ModuleEntry> {
        self.modules.iter_mut()
    }
}
