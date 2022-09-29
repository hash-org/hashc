//! Hash Compiler sources map and interfaces for accessing and storing
//! job sources.
use std::{
    collections::{
        hash_map::{Iter, IterMut},
        HashMap, HashSet,
    },
    path::{Path, PathBuf},
};

use hash_ast::{
    ast,
    ast::{AstVisitor, OwnsAstNode},
    tree::AstTreeGenerator,
};
use hash_source::{InteractiveId, ModuleId, ModuleKind, SourceId, SourceMap};
use hash_types::storage::{GlobalStorage, LocalStorage};
use hash_utils::{path::adjust_canonicalisation, tree_writing::TreeWriter};

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

/// Represents a module that was added to the [NodeMap]. [Module] holds
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

    /// Get the `path` from the [Module].
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

/// Union of a [Source] within [NodeMap]. It can either be a [Module]
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

    /// /// Create an [Iter] over the currently stores modules within [NodeMap]
    pub fn iter_modules(&self) -> Iter<'_, ModuleId, Module> {
        self.modules.iter()
    }

    /// Create an [IterMut] over the currently stores modules within [NodeMap].
    pub fn iter_mut_modules(&mut self) -> IterMut<'_, ModuleId, Module> {
        self.modules.iter_mut()
    }
}

/// Storage that is used by stages that need to access type information about
/// modules in the current workspace.
#[derive(Debug)]
pub struct TyStorage {
    /// Storage that is used by the typechecker to resolve local items
    /// within certain contexts.
    pub local: LocalStorage,

    /// Persistent storage of all data structures that is emitted by the
    /// typechecking stage, and possibly further stages.
    pub global: GlobalStorage,
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

    pub desugared_modules: HashSet<SourceId>,

    /// Modules that have already been semantically checked. This is needed in
    /// order to avoid re-checking modules on re-evaluations of a workspace.
    pub semantically_checked_modules: HashSet<SourceId>,

    pub ty_storage: TyStorage,
}

impl Default for Workspace {
    fn default() -> Self {
        Self::new()
    }
}

impl Workspace {
    /// Create a new [Workspace], initialising all members to be empty.
    pub fn new() -> Self {
        let global = GlobalStorage::new();
        let local = LocalStorage::new(&global, SourceId::default());

        Self {
            ty_storage: TyStorage { global, local },
            node_map: NodeMap::new(),
            source_map: SourceMap::new(),
            dependencies: HashMap::new(),
            desugared_modules: HashSet::new(),
            semantically_checked_modules: HashSet::new(),
        }
    }

    /// Add a interactive block to the [Workspace] by providing the contents and
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

    /// Add a module to the [Workspace] by providing the contents and the
    /// [Module]. Returns the created [ModuleId] from adding it to the
    /// source map.
    pub fn add_module(&mut self, contents: String, module: Module, kind: ModuleKind) -> ModuleId {
        let id = self.source_map.add_module(module.path.to_owned(), contents, kind);
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

    /// Get a mutable reference to [SourceMap]
    pub fn source_map_mut(&mut self) -> &mut SourceMap {
        &mut self.source_map
    }

    /// Get a reference to [NodeMap]
    pub fn node_map(&self) -> &NodeMap {
        &self.node_map
    }

    /// Get a mutable reference to [NodeMap]
    pub fn node_map_mut(&mut self) -> &mut NodeMap {
        &mut self.node_map
    }

    /// Get the [TyStorage] stored within the [Workspace].
    pub fn ty_storage(&self) -> &TyStorage {
        &self.ty_storage
    }

    /// Utility function used by AST-like stages in order to print the
    /// current [self::sources::NodeMap].
    pub fn print_sources(&self, entry_point: SourceId) {
        match entry_point {
            SourceId::Interactive(id) => {
                // If this is an interactive statement, we want to print the statement that was
                // just parsed.
                let source = self.node_map().get_interactive_block(id);
                let tree = AstTreeGenerator.visit_body_block(source.node_ref()).unwrap();

                println!("{}", TreeWriter::new(&tree));
            }
            SourceId::Module(_) => {
                // If this is a module, we want to print all of the generated modules from the
                // parsing stage
                for (_, generated_module) in self.node_map().iter_modules() {
                    let tree = AstTreeGenerator.visit_module(generated_module.node_ref()).unwrap();

                    println!(
                        "Tree for `{}`:\n{}",
                        adjust_canonicalisation(generated_module.path()),
                        TreeWriter::new(&tree)
                    );
                }
            }
        }
    }
}
