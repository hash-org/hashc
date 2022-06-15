//! Hash Compiler sources map and interfaces for accessing and storing
//! job sources.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use hash_ast::ast;
use hash_source::{InteractiveId, ModuleId, SourceId, SourceMap};
use slotmap::{
    basic::{Iter, IterMut},
    SlotMap,
};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

#[derive(Debug)]
pub struct InteractiveBlock {
    contents: String,
    node: Option<ast::AstNode<ast::BodyBlock>>,
}

impl InteractiveBlock {
    pub fn new(contents: String) -> Self {
        Self {
            contents,
            node: None,
        }
    }

    pub fn node(&self) -> ast::AstNodeRef<ast::BodyBlock> {
        self.node.as_ref().unwrap().ast_ref()
    }

    /// Get a [AstNodeRefMut] to the inner [ast::BodyBlock]
    pub fn node_mut(&mut self) -> ast::AstNodeRefMut<ast::BodyBlock> {
        self.node.as_mut().unwrap().ast_ref_mut()
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn set_node(&mut self, node: ast::AstNode<ast::BodyBlock>) {
        self.node = Some(node);
    }
}

#[derive(Debug)]
pub struct Module {
    path: PathBuf,
    contents: Option<String>,
    node: Option<ast::AstNode<ast::Module>>,
}

impl Module {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            contents: None,
            node: None,
        }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn node(&self) -> ast::AstNodeRef<ast::Module> {
        self.node.as_ref().unwrap().ast_ref()
    }

    pub fn node_mut(&mut self) -> &mut ast::Module {
        self.node.as_mut().unwrap()
    }

    pub fn contents(&self) -> &str {
        self.contents.as_ref().unwrap()
    }

    pub fn set_node(&mut self, node: ast::AstNode<ast::Module>) {
        self.node = Some(node);
    }

    pub fn set_contents(&mut self, contents: String) {
        self.contents = Some(contents);
    }
}

#[derive(Debug)]
pub enum Source {
    Interactive(InteractiveBlock),
    Module(Module),
}

#[derive(Debug, Copy, Clone)]
pub enum SourceRef<'i> {
    Interactive(&'i InteractiveBlock),
    Module(&'i Module),
}

#[derive(Debug, Default)]
pub struct Sources {
    interactive_offset: usize,
    interactive_blocks: SlotMap<InteractiveId, InteractiveBlock>,
    modules: SlotMap<ModuleId, Module>,
    module_paths: HashMap<PathBuf, ModuleId>,
    dependencies: HashMap<SourceId, HashSet<ModuleId>>,
}

impl Sources {
    pub fn new() -> Self {
        Self {
            interactive_offset: 0,
            interactive_blocks: SlotMap::with_key(),
            modules: SlotMap::with_key(),
            module_paths: HashMap::new(),
            dependencies: HashMap::new(),
        }
    }

    pub fn add_interactive_block(&mut self, interactive_block: InteractiveBlock) -> InteractiveId {
        self.interactive_offset += interactive_block.contents.len();
        self.interactive_blocks.insert(interactive_block)
    }

    pub fn add_module(&mut self, module: Module) -> ModuleId {
        let module_path = module.path.to_owned();
        let module_id = self.modules.insert(module);
        self.module_paths.insert(module_path, module_id);
        module_id
    }

    pub fn add_source(&mut self, source: Source) -> SourceId {
        match source {
            Source::Interactive(interactive_block) => {
                SourceId::Interactive(self.add_interactive_block(interactive_block))
            }
            Source::Module(module) => SourceId::Module(self.add_module(module)),
        }
    }

    pub fn get_interactive_block(&self, interactive_id: InteractiveId) -> &InteractiveBlock {
        self.interactive_blocks.get(interactive_id).unwrap()
    }

    pub fn get_interactive_block_mut(
        &mut self,
        interactive_id: InteractiveId,
    ) -> &mut InteractiveBlock {
        self.interactive_blocks.get_mut(interactive_id).unwrap()
    }

    pub fn get_module_mut(&mut self, module_id: ModuleId) -> &mut Module {
        self.modules.get_mut(module_id).unwrap()
    }

    pub fn get_module(&self, module_id: ModuleId) -> &Module {
        self.modules.get(module_id).unwrap()
    }

    pub fn get_module_id_by_path(&self, path: &Path) -> Option<ModuleId> {
        self.module_paths.get(path).copied()
    }

    pub fn get_module_by_path(&self, path: &Path) -> Option<&Module> {
        Some(self.get_module(self.get_module_id_by_path(path)?))
    }

    /// Function to iterate over the modules that are currently
    /// present within the sources.
    pub fn iter_modules(&self) -> Iter<'_, ModuleId, Module> {
        self.modules.iter()
    }

    pub fn iter_mut_modules(&mut self) -> IterMut<'_, ModuleId, Module> {
        self.modules.iter_mut()
    }

    pub fn get_source(&self, source_id: SourceId) -> SourceRef<'_> {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                SourceRef::Interactive(self.get_interactive_block(interactive_id))
            }
            SourceId::Module(module_id) => SourceRef::Module(self.get_module(module_id)),
        }
    }

    pub fn add_dependency(&mut self, source_id: SourceId, dependency: ModuleId) {
        self.dependencies
            .entry(source_id)
            .or_insert_with(HashSet::new)
            .insert(dependency);
    }
}

impl SourceMap for Sources {
    fn path_by_id(&self, source_id: SourceId) -> &Path {
        match self.get_source(source_id) {
            SourceRef::Interactive(_) => Path::new("<interactive>"),
            SourceRef::Module(module) => module.path(),
        }
    }

    fn contents_by_id(&self, source_id: SourceId) -> &str {
        match self.get_source(source_id) {
            SourceRef::Interactive(interactive) => interactive.contents(),
            SourceRef::Module(module) => module.contents(),
        }
    }
}
