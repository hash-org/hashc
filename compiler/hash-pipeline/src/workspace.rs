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

use hash_ast::{
    ast::{AstVisitor, OwnsAstNode},
    node_map::{InteractiveBlock, ModuleEntry, NodeMap},
    tree::AstTreeGenerator,
};
use hash_source::{InteractiveId, ModuleId, ModuleKind, SourceId, SourceMap};
use hash_utils::tree_writing::TreeWriter;

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
    pub fn add_module(
        &mut self,
        contents: String,
        module: ModuleEntry,
        kind: ModuleKind,
    ) -> ModuleId {
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

    /// Utility function used by AST-like stages in order to print the
    /// current [NodeMap].
    pub fn print_sources(&self, entry_point: SourceId) {
        match entry_point {
            SourceId::Interactive(id) => {
                // If this is an interactive statement, we want to print the statement that was
                // just parsed.
                let source = self.node_map.get_interactive_block(id);
                let tree = AstTreeGenerator.visit_body_block(source.node_ref()).unwrap();

                println!("{}", TreeWriter::new(&tree));
            }
            SourceId::Module(_) => {
                // If this is a module, we want to print all of the generated modules from the
                // parsing stage
                for (_, generated_module) in self.node_map.iter_modules() {
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
}
