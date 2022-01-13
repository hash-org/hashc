//! Hash compiler data structures for storing parsed modules
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use crate::ast;
use dashmap::{lock::RwLock, DashMap, ReadOnlyView};
use hash_source::{SourceId, SourceMap};
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};
/// Creates a set of loaded modules.
#[derive(Debug, Default)]
pub struct ModuleBuilder<'c> {
    indexes: DashMap<SourceId, ()>,
    path_to_index: DashMap<PathBuf, SourceId>,
    filenames_by_index: DashMap<SourceId, PathBuf>,
    modules_by_index: DashMap<SourceId, ast::AstNode<'c, ast::Module<'c>>>,
    contents_by_index: DashMap<SourceId, String>,
    deps_by_index: DashMap<SourceId, DashMap<SourceId, ()>>,
    entry_point: RwLock<Option<SourceId>>,
}

impl<'c> ModuleBuilder<'c> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_module_at(&self, index: SourceId, node: ast::AstNode<'c, ast::Module<'c>>) {
        self.modules_by_index.insert(index, node);
    }

    pub fn add_contents(&self, index: SourceId, path: PathBuf, contents: String) {
        self.path_to_index.insert(path.clone(), index);
        self.contents_by_index.insert(index, contents);
        self.filenames_by_index.insert(index, path);
    }

    pub fn reserve_index(&self) -> SourceId {
        let next = SourceId::new();
        self.indexes.insert(next, ());
        self.deps_by_index.insert(next, DashMap::new());
        next
    }

    pub fn set_entry_point(&self, index: SourceId) {
        let mut entry = self.entry_point.write();
        *entry = Some(index);
    }

    pub fn add_dependency(&self, parent: SourceId, child: SourceId) {
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
    indexes: ReadOnlyView<SourceId, ()>,
    path_to_index: ReadOnlyView<PathBuf, SourceId>,
    filenames_by_index: ReadOnlyView<SourceId, PathBuf>,
    modules_by_index: ReadOnlyView<SourceId, ast::AstNode<'c, ast::Module<'c>>>,
    contents_by_index: ReadOnlyView<SourceId, String>,
    deps_by_index: HashMap<SourceId, ReadOnlyView<SourceId, ()>>,
    entry_point: Option<SourceId>,
}

impl SourceMap for Modules<'_> {
    fn path_by_index(&self, index: SourceId) -> &Path {
        self.get_by_index(index).filename()
    }

    fn contents_by_index(&self, index: SourceId) -> &str {
        self.get_by_index(index).content()
    }
}

impl<'c> Modules<'c> {
    pub fn has_path(&self, path: impl AsRef<Path>) -> bool {
        self.path_to_index.contains_key(path.as_ref())
    }

    // pub fn sources(&self) -> SourceMap {
    //     let mut map = HashMap::with_capacity(self.filenames_by_index.len());

    //     self.filenames_by_index.iter().for_each(|key| {
    //         let contents = self.contents_by_index.get(key.0).unwrap();

    //         // @@Copying
    //         map.insert(
    //             *key.0,
    //             SourceModule::new(key.1.to_owned(), contents.to_owned()),
    //         );
    //     });

    //     SourceMap::new(map)
    // }

    pub fn has_entry_point(&self) -> bool {
        self.entry_point.is_some()
    }

    pub fn get_entry_point<'m>(&'m self) -> Option<Module<'c, 'm>> {
        Some(self.get_by_index(self.entry_point?))
    }

    pub fn get_entry_point_unchecked<'m>(&'m self) -> Module<'c, 'm> {
        self.get_entry_point().unwrap()
    }

    pub fn get_by_index<'m>(&'m self, index: SourceId) -> Module<'c, 'm> {
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

    pub fn has_index(&self, index: SourceId) -> bool {
        self.indexes.contains_key(&index)
    }
}

/// Represents a single module.
pub struct Module<'c, 'm> {
    index: SourceId,
    modules: &'m Modules<'c>,
}

impl<'c, 'm> Module<'c, 'm> {
    pub fn all_modules(&self) -> &Modules<'c> {
        self.modules
    }

    pub fn index(&self) -> SourceId {
        self.index
    }

    pub fn is_entry_point(&self) -> bool {
        self.modules.entry_point == Some(self.index)
    }

    pub fn ast_checked(&self) -> Option<ast::AstNodeRef<ast::Module<'c>>> {
        self.modules
            .modules_by_index
            .get(&self.index)
            .map(|a| a.ast_ref())
    }

    pub fn ast(&self) -> ast::AstNodeRef<ast::Module<'c>> {
        self.ast_checked().unwrap()
    }

    pub fn content(&self) -> &'m str {
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

    pub fn filename(&self) -> &'m Path {
        self.modules
            .filenames_by_index
            .get(&self.index)
            .unwrap()
            .as_ref()
    }
}
