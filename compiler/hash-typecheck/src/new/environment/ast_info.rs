use std::hash::Hash;

use bimap::BiMap;
use hash_ast::ast::AstNodeId;
use hash_types::{
    mods::ModDefId,
    new::{data::DataDefId, fns::FnDefId, scopes::StackId},
};

/// A partial mapping from AST nodes to [`T`] and back.
#[derive(Debug, Clone)]
pub struct AstMap<T: Hash + Eq> {
    data: BiMap<AstNodeId, T>,
}

impl<T: Hash + Eq> AstMap<T> {
    pub fn new() -> Self {
        Self { data: BiMap::new() }
    }

    pub fn insert(&mut self, ast_id: AstNodeId, data: T) {
        self.data.insert(ast_id, data);
    }

    pub fn get_data_ref_by_node(&self, ast_id: AstNodeId) -> Option<&T> {
        self.data.get_by_left(&ast_id)
    }

    pub fn get_node_by_data_ref(&self, data: &T) -> Option<AstNodeId> {
        self.data.get_by_right(data).copied()
    }
}

impl<T: Hash + Eq> Default for AstMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Hash + Eq + Copy> AstMap<T> {
    pub fn get_data_by_node(&self, ast_id: AstNodeId) -> Option<T> {
        self.data.get_by_left(&ast_id).copied()
    }

    pub fn get_node_by_data(&self, data: T) -> Option<AstNodeId> {
        self.data.get_by_right(&data).copied()
    }
}

#[derive(Debug, Clone)]
pub struct AstInfo {
    pub data_defs: AstMap<DataDefId>,
    pub mod_defs: AstMap<ModDefId>,
    pub fn_defs: AstMap<FnDefId>,
    pub stacks: AstMap<StackId>,
}
