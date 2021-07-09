use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use hash_utils::counter;

use crate::ast;

counter! {
    name: ModuleIdx,
    counter_name: MODULE_COUNTER,
    visibility: pub,
    method_visibility: pub(crate),
}

/// Represents a set of loaded modules.
#[derive(Debug, Default)]
pub struct Modules {
    indexes: HashSet<ModuleIdx>,
    path_to_index: HashMap<PathBuf, ModuleIdx>,
    filenames_by_index: HashMap<ModuleIdx, PathBuf>,
    modules_by_index: HashMap<ModuleIdx, ast::Module>,
    contents_by_index: HashMap<ModuleIdx, String>,
    deps_by_index: HashMap<ModuleIdx, HashSet<ModuleIdx>>,
    entry_point: Option<ModuleIdx>,
}

impl Modules {
    /// Create a new [Modules] object
    pub fn new() -> Self {
        Modules::default()
    }

    pub fn has_path(&self, path: impl AsRef<Path>) -> bool {
        self.path_to_index.contains_key(path.as_ref())
    }

    pub fn has_entry_point(&self) -> bool {
        self.entry_point.is_some()
    }

    pub fn get_entry_point(&self) -> Option<Module<'_>> {
        Some(self.get_by_index(self.entry_point?))
    }

    pub fn get_entry_point_unchecked(&self) -> Module<'_> {
        self.get_entry_point().unwrap()
    }

    pub fn get_by_index(&self, index: ModuleIdx) -> Module<'_> {
        Module {
            index,
            modules: self,
        }
    }

    pub fn get_by_path(&self, path: impl AsRef<Path>) -> Option<Module<'_>> {
        self.path_to_index
            .get(path.as_ref())
            .map(|&idx| self.get_by_index(idx))
    }

    pub fn get_by_path_unchecked(&self, path: impl AsRef<Path>) -> Module<'_> {
        self.get_by_path(path).unwrap()
    }

    pub(crate) fn add_module(&mut self, path: PathBuf, contents: String) -> Module<'_> {
        let index = self.reserve_index();
        self.add_module_at(index, path, contents)
    }

    pub(crate) fn set_node(&mut self, index: ModuleIdx, node: ast::Module) {
        self.modules_by_index.insert(index, node);
    }

    pub(crate) fn add_module_at(
        &mut self,
        index: ModuleIdx,
        path: PathBuf,
        contents: String,
    ) -> Module<'_> {
        self.path_to_index.insert(path.clone(), index);
        self.filenames_by_index.insert(index, path);
        self.contents_by_index.insert(index, contents);

        Module {
            index,
            modules: self,
        }
    }

    pub(crate) fn reserve_index(&mut self) -> ModuleIdx {
        let next = ModuleIdx::new();
        self.indexes.insert(next);
        self.deps_by_index.insert(next, HashSet::new());
        next
    }

    pub(crate) fn set_entry_point(&mut self, index: ModuleIdx) {
        self.entry_point = Some(index);
    }

    pub fn add_dependency(&mut self, parent: ModuleIdx, child: ModuleIdx) {
        self.deps_by_index.get_mut(&parent).unwrap().insert(child);
    }

    pub fn iter(&self) -> impl Iterator<Item = Module<'_>> {
        self.filenames_by_index.keys().map(move |&index| Module {
            index,
            modules: self,
        })
    }
}

/// Represents a single module.
pub struct Module<'modules> {
    index: ModuleIdx,
    modules: &'modules Modules,
}

impl<'modules> Module<'modules> {
    pub fn all_modules(&self) -> &Modules {
        self.modules
    }

    pub fn index(&self) -> ModuleIdx {
        self.index
    }

    pub fn is_entry_point(&self) -> bool {
        self.modules.entry_point == Some(self.index)
    }

    pub fn ast_checked(&self) -> Option<&ast::Module> {
        self.modules.modules_by_index.get(&self.index)
    }

    pub fn ast(&self) -> &ast::Module {
        self.ast_checked().unwrap()
    }

    pub fn content(&self) -> &str {
        self.modules
            .contents_by_index
            .get(&self.index)
            .unwrap()
            .as_ref()
    }

    pub fn dependencies(&'modules self) -> impl Iterator<Item = Module<'modules>> {
        self.modules
            .deps_by_index
            .get(&self.index)
            .unwrap()
            .iter()
            .map(move |&index| Module {
                index,
                modules: self.modules,
            })
    }

    pub fn filename(&self) -> &Path {
        self.modules
            .filenames_by_index
            .get(&self.index)
            .unwrap()
            .as_ref()
    }
}
