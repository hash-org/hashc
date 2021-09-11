//! Hash compiler data structures for storing parsed modules
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::ast;
use dashmap::{lock::RwLock, DashMap, ReadOnlyView};
use hash_utils::counter;
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

counter! {
    name: ModuleIdx,
    counter_name: MODULE_COUNTER,
    visibility: pub,
    method_visibility: pub(crate),
}

/// Creates a set of loaded modules.
#[derive(Debug, Default)]
pub struct ModuleBuilder<'c> {
    indexes: DashMap<ModuleIdx, ()>,
    path_to_index: DashMap<PathBuf, ModuleIdx>,
    filenames_by_index: DashMap<ModuleIdx, PathBuf>,
    modules_by_index: DashMap<ModuleIdx, ast::Module<'c>>,
    contents_by_index: DashMap<ModuleIdx, String>,
    deps_by_index: DashMap<ModuleIdx, DashMap<ModuleIdx, ()>>,
    entry_point: RwLock<Option<ModuleIdx>>,
}

impl<'c> ModuleBuilder<'c> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_module_at(
        &self,
        index: ModuleIdx,
        // path: PathBuf,
        node: ast::Module<'c>,
    ) {
        // self.path_to_index.insert(path.clone(), index);
        // self.filenames_by_index.insert(index, path);
        // self.contents_by_index.insert(index, contents);
        self.modules_by_index.insert(index, node);
    }

    pub fn add_contents(&self, index: ModuleIdx, path: PathBuf, contents: String) {
        self.path_to_index.insert(path.clone(), index);
        self.contents_by_index.insert(index, contents);
        self.filenames_by_index.insert(index, path);
    }

    pub fn reserve_index(&self) -> ModuleIdx {
        let next = ModuleIdx::new();
        self.indexes.insert(next, ());
        self.deps_by_index.insert(next, DashMap::new());
        next
    }

    pub fn set_entry_point(&self, index: ModuleIdx) {
        let mut entry = self.entry_point.write();
        *entry = Some(index);
    }

    pub fn add_dependency(&self, parent: ModuleIdx, child: ModuleIdx) {
        self.deps_by_index.get(&parent).unwrap().insert(child, ());
    }

    pub fn build(self) -> Modules<'c> {
        Modules {
            indexes: self.indexes.into_read_only(),
            path_to_index: self.path_to_index.into_read_only(),
            filenames_by_index: self.filenames_by_index.into_read_only(),
            modules_by_index: self.modules_by_index.into_read_only(),
            contents_by_index: self.contents_by_index.into_read_only(),
            // @@Speed: This is unfortunate, especially since ReadOnlyView should be the same
            // layout as DashMap.
            deps_by_index: self
                .deps_by_index
                .into_iter()
                .map(|(k, v)| (k, v.into_read_only()))
                .collect(),
            entry_point: self.entry_point.into_inner(),
        }
    }
}

/// Represents a set of loaded modules.
#[derive(Debug)]
pub struct Modules<'c> {
    indexes: ReadOnlyView<ModuleIdx, ()>,
    path_to_index: ReadOnlyView<PathBuf, ModuleIdx>,
    filenames_by_index: ReadOnlyView<ModuleIdx, PathBuf>,
    modules_by_index: ReadOnlyView<ModuleIdx, ast::Module<'c>>,
    contents_by_index: ReadOnlyView<ModuleIdx, String>,
    deps_by_index: HashMap<ModuleIdx, ReadOnlyView<ModuleIdx, ()>>,
    entry_point: Option<ModuleIdx>,
}

impl<'c> Modules<'c> {
    pub fn has_path(&self, path: impl AsRef<Path>) -> bool {
        self.path_to_index.contains_key(path.as_ref())
    }

    pub fn has_entry_point(&self) -> bool {
        self.entry_point.is_some()
    }

    pub fn get_entry_point<'m>(&'m self) -> Option<Module<'c, 'm>> {
        Some(self.get_by_index(self.entry_point?))
    }

    pub fn get_entry_point_unchecked<'m>(&'m self) -> Module<'c, 'm> {
        self.get_entry_point().unwrap()
    }

    pub fn get_by_index<'m>(&'m self, index: ModuleIdx) -> Module<'c, 'm> {
        Module {
            index,
            modules: self,
        }
    }

    pub fn get_by_path<'m>(&'m self, path: impl AsRef<Path>) -> Option<Module<'c, 'm>> {
        self.path_to_index
            .get(path.as_ref())
            .map(|&idx| self.get_by_index(idx))
    }

    pub fn get_by_path_unchecked<'m>(&'m self, path: impl AsRef<Path>) -> Module<'c, 'm> {
        self.get_by_path(path).unwrap()
    }

    pub fn iter<'m>(&'m self) -> impl Iterator<Item = Module<'c, 'm>> {
        self.filenames_by_index.keys().map(move |&index| Module {
            index,
            modules: self,
        })
    }
}

/// Represents a single module.
pub struct Module<'c, 'm> {
    index: ModuleIdx,
    modules: &'m Modules<'c>,
}

impl<'c, 'm> Module<'c, 'm> {
    pub fn all_modules(&self) -> &Modules<'c> {
        self.modules
    }

    pub fn index(&self) -> ModuleIdx {
        self.index
    }

    pub fn is_entry_point(&self) -> bool {
        self.modules.entry_point == Some(self.index)
    }

    pub fn ast_checked(&self) -> Option<&ast::Module<'c>> {
        self.modules.modules_by_index.get(&self.index)
    }

    pub fn ast(&self) -> &ast::Module<'c> {
        self.ast_checked().unwrap()
    }

    pub fn content(&self) -> &str {
        self.modules
            .contents_by_index
            .get(&self.index)
            .unwrap()
            .as_ref()
    }

    pub fn dependencies(&self) -> impl Iterator<Item = Module<'c, '_>> {
        self.modules
            .deps_by_index
            .get(&self.index)
            .unwrap()
            .iter()
            .map(move |(&index, _)| Module {
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
