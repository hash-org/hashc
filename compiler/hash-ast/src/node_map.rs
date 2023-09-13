//! Defines a data structure that holds all of the nodes that have been parsed.
//! This is used to ensure that the same node is not parsed and to retrieve
//! nodes in later compilation stages.
use std::{
    path::{Path, PathBuf},
    slice::{Iter, IterMut},
};

use hash_source::{InteractiveId, ModuleId, SourceId};
use hash_utils::index_vec::{index_vec, IndexVec};

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
    node: AstNode<Module>,
}

impl ModuleEntry {
    /// Create a new [ModuleEntry] with a specified `path` and the `node being
    /// set to [None].
    pub fn new(path: PathBuf, node: AstNode<Module>) -> Self {
        Self { path, node }
    }

    /// Get the `path` from the [Module].
    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl OwnsAstNode<Module> for ModuleEntry {
    /// Get a reference to node within [ModuleEntry]. This
    /// assumes that the node had already been set.
    fn node(&self) -> &AstNode<Module> {
        &self.node
    }

    /// Get a mutable reference to node within [ModuleEntry]. This
    /// assumes that the node had already been set.
    fn node_mut(&mut self) -> &mut AstNode<Module> {
        &mut self.node
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
    modules: IndexVec<ModuleId, ModuleEntry>,
    /// All [InteractiveBlock] nodes that have been parsed.
    interactive_blocks: IndexVec<InteractiveId, InteractiveBlock>,
}

/// Convenience trait for types that have mutable access to a [NodeMap].
pub trait HasNodeMapMut: HasNodeMap {
    /// Get a mutable reference to the [NodeMap].
    fn node_map_mut(&mut self) -> &mut NodeMap;
}

/// Convenience trait for types that have access to a [NodeMap].
pub trait HasNodeMap {
    /// Get a reference to the [NodeMap].
    fn node_map(&self) -> &NodeMap;
}

impl NodeMap {
    /// Create a new [NodeMap]
    pub fn new() -> Self {
        Self { modules: index_vec![], interactive_blocks: index_vec![] }
    }

    /// Add a [InteractiveBlock] to the [NodeMap]
    pub fn add_interactive_block(&mut self, block: InteractiveBlock) {
        self.interactive_blocks.push(block);
    }

    /// Add a [Module] to the [NodeMap]
    pub fn add_module(&mut self, module: ModuleEntry) {
        self.modules.push(module);
    }

    /// Get a [SourceRef] by [SourceId].
    pub fn get_source(&self, id: SourceId) -> SourceRef<'_> {
        if id.is_interactive() {
            SourceRef::Interactive(self.get_interactive_block(id.into()))
        } else {
            SourceRef::Module(self.get_module(id.into()))
        }
    }

    /// Get a reference to an [InteractiveBlock], panics if the [InteractiveId]
    /// has no backing [InteractiveBlock].
    pub fn get_interactive_block(&self, id: InteractiveId) -> &InteractiveBlock {
        self.interactive_blocks.get(id).unwrap()
    }

    /// Get a mutable reference to an [InteractiveBlock], panics if the
    /// [InteractiveId] has no backing [InteractiveBlock].
    pub fn get_interactive_block_mut(&mut self, id: InteractiveId) -> &mut InteractiveBlock {
        self.interactive_blocks.get_mut(id).unwrap()
    }

    /// Get a mutable reference to an [Module], panics if the [SourceId]
    /// has no backing [Module].
    pub fn get_module(&self, id: ModuleId) -> &ModuleEntry {
        self.modules.get(id).unwrap()
    }

    /// Get a reference to an [Module], panics if the [SourceId]
    /// has no backing [Module].
    pub fn get_module_mut(&mut self, id: ModuleId) -> &mut ModuleEntry {
        self.modules.get_mut(id).unwrap()
    }

    /// /// Create an [Iter] over the currently stores modules within [NodeMap]
    pub fn iter_modules(&self) -> Iter<ModuleEntry> {
        self.modules.iter()
    }

    /// Create an [IterMut] over the currently stores modules within [NodeMap].
    pub fn iter_mut_modules(&mut self) -> IterMut<ModuleEntry> {
        self.modules.iter_mut()
    }
}
