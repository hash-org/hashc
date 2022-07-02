//! Hash Compiler sources map and interfaces for accessing and storing
//! job sources.
use hash_ast::ast;
use hash_source::{InteractiveId, ModuleId, SourceId, SourceMap};
use std::{
    collections::{
        hash_map::{Iter, IterMut},
        HashMap, HashSet,
    },
    path::{Path, PathBuf},
};

/// Data structure which holds information and compiler stage results for a
/// particular interactive block. Currently, this only stores the generated
/// [ast::AstNode<ast::BodyBlock>] from parsing.
#[derive(Debug, Default)]
pub struct InteractiveBlock {
    /// The generated node, only filled in when parsing is complete.
    node: Option<ast::AstNode<ast::BodyBlock>>,
}

impl InteractiveBlock {
    /// Create a new [InteractiveBlock]. Initially sets the `node` as being
    /// [None].
    pub fn new() -> Self {
        Self { node: None }
    }

    /// Set the `node` for given [InteractiveBlock]
    pub fn set_node(&mut self, node: ast::AstNode<ast::BodyBlock>) {
        self.node = Some(node);
    }
}

impl ast::OwnsAstNode<ast::BodyBlock> for InteractiveBlock {
    /// Get a reference to node within [InteractiveBlock]. This
    /// assumes that the node had already been set.
    fn node(&self) -> &ast::AstNode<ast::BodyBlock> {
        self.node.as_ref().unwrap()
    }

    /// Get a mutable reference to node within [InteractiveBlock]. This
    /// assumes that the node had already been set.
    fn node_mut(&mut self) -> &mut ast::AstNode<ast::BodyBlock> {
        self.node.as_mut().unwrap()
    }
}

/// Represents a module that was added to the [Sources]. [Module] holds
/// meta data about the module, such as the path. It also holds the
/// parsed [ast::AstNode<ast::Module>] within the data structure. This is
/// set to being optional because it is likely that the generated AST
/// is added later.
#[derive(Debug)]
pub struct Module {
    /// The absolute path of the module on disk.
    path: PathBuf,
    /// The generated AST for the module, set when parsing is complete.
    node: Option<ast::AstNode<ast::Module>>,
}

impl Module {
    /// Create a new [Module] with a specified `path` and the `node being set to
    /// [None].
    pub fn new(path: PathBuf) -> Self {
        Self { path, node: None }
    }

    /// Get that `path` from the [Module].
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Set the `node` for given [Module]
    pub fn set_node(&mut self, node: ast::AstNode<ast::Module>) {
        self.node = Some(node);
    }
}

impl ast::OwnsAstNode<ast::Module> for Module {
    /// Get a reference to node within [Module]. This
    /// assumes that the node had already been set.
    fn node(&self) -> &ast::AstNode<ast::Module> {
        self.node.as_ref().unwrap()
    }

    /// Get a mutable reference to node within [Module]. This
    /// assumes that the node had already been set.
    fn node_mut(&mut self) -> &mut ast::AstNode<ast::Module> {
        self.node.as_mut().unwrap()
    }
}

/// Union of a [Source] within [Sources]. It can either be a [Module]
/// or [InteractiveBlock].
#[derive(Debug)]
pub enum Source {
    /// If the source is an [InteractiveBlock]
    Interactive(InteractiveBlock),
    /// If the source is an [Module]
    Module(Module),
}

/// Wrapper for [Source] in order to get a reference to the
/// enclosed module or interactive block.
#[derive(Debug, Copy, Clone)]
pub enum SourceRef<'i> {
    /// If the source is an [InteractiveBlock]
    Interactive(&'i InteractiveBlock),
    /// If the source is an [Module]
    Module(&'i Module),
}

#[derive(Debug, Default)]
pub struct NodeMap {
    modules: HashMap<ModuleId, Module>,
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
    pub fn add_module(&mut self, id: ModuleId, module: Module) {
        self.modules.insert(id, module);
    }

    /// Get a reference to an [InteractiveBlock], panics if the [InteractiveId]
    /// has no backing [InteractiveBlock].
    pub fn get_interactive_block(&self, interactive_id: InteractiveId) -> &InteractiveBlock {
        self.interactive_blocks.get(&interactive_id).unwrap()
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

    /// Get a mutable reference to an [InteractiveBlock], panics if the
    /// [InteractiveId] has no backing [InteractiveBlock].
    pub fn get_interactive_block_mut(
        &mut self,
        interactive_id: InteractiveId,
    ) -> &mut InteractiveBlock {
        self.interactive_blocks.get_mut(&interactive_id).unwrap()
    }

    /// Get a reference to an [Module], panics if the [ModuleId]
    /// has no backing [Module].
    pub fn get_module_mut(&mut self, module_id: ModuleId) -> &mut Module {
        self.modules.get_mut(&module_id).unwrap()
    }

    /// Get a mutable reference to an [Module], panics if the [ModuleId]
    /// has no backing [Module].
    pub fn get_module(&self, module_id: ModuleId) -> &Module {
        self.modules.get(&module_id).unwrap()
    }

    /// /// Create an [Iter] over the currently stores modules within [Sources]
    pub fn iter_modules(&self) -> Iter<'_, ModuleId, Module> {
        self.modules.iter()
    }

    /// Create an [IterMut] over the currently stores modules within [Sources].
    pub fn iter_mut_modules(&mut self) -> IterMut<'_, ModuleId, Module> {
        self.modules.iter_mut()
    }
}

#[derive(Debug, Default)]
pub struct Sources {
    /// Dependency map between sources and modules.
    dependencies: HashMap<SourceId, HashSet<ModuleId>>,
    /// Stores all of the raw file contents of the interactive blocks and
    /// modules.
    pub source_map: SourceMap,
    /// Stores all of the generated AST for modules and nodes
    pub node_map: NodeMap,
}

impl Sources {
    /// Create a new [Sources], initialising all members to be empty.
    pub fn new() -> Self {
        Self {
            node_map: NodeMap::new(),
            source_map: SourceMap::new(),
            dependencies: HashMap::new(),
        }
    }

    /// Add a interactive block to the [Sources] by providing the contents and
    /// the [InteractiveBlock]. Returns the created [InteractiveId] from
    /// adding it to the source map.
    pub fn add_interactive_block(
        &mut self,
        input: String,
        block: InteractiveBlock,
    ) -> InteractiveId {
        let id = self.source_map.add_interactive_block(input);
        self.node_map.add_interactive_block(id, block);

        id
    }

    /// Add a module to the [Sources] by providing the contents and the
    /// [Module]. Returns the created [ModuleId] from adding it to the
    /// source map.
    pub fn add_module(&mut self, contents: String, module: Module) -> ModuleId {
        let id = self.source_map.add_module(module.path.to_owned(), contents);
        self.node_map.add_module(id, module);

        id
    }

    /// Get the [ModuleId] of the module by the specified [Path].
    pub fn get_module_id_by_path(&self, path: &Path) -> Option<ModuleId> {
        self.source_map.get_module_id_by_path(path)
    }

    /// Add a module dependency specified by a [ModuleId] to a specific source
    /// specified by a [SourceId].
    pub fn add_dependency(&mut self, source_id: SourceId, dependency: ModuleId) {
        self.dependencies.entry(source_id).or_insert_with(HashSet::new).insert(dependency);
    }

    /// Get a reference to [SourceMap]
    pub fn source_map(&self) -> &SourceMap {
        &self.source_map
    }

    /// Get a reference to [NodeMap]
    pub fn node_map(&self) -> &NodeMap {
        &self.node_map
    }

    /// Get a mutable reference to [NodeMap]
    pub fn node_map_mut(&mut self) -> &mut NodeMap {
        &mut self.node_map
    }
}
