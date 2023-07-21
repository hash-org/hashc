use std::hash::Hash;

use bimap::BiMap;
use hash_ast::ast::AstNodeId;
use hash_utils::parking_lot::RwLock;

use crate::{
    args::ArgId,
    context::Decl,
    data::{CtorDefId, DataDefId},
    fns::FnDefId,
    mods::{ModDefId, ModMemberId},
    params::ParamId,
    pats::PatId,
    scopes::StackId,
    terms::TermId,
    tys::TyId,
};

/// A partial mapping from AST nodes to `T` and back.
#[derive(Debug)]
pub struct AstMap<T: Hash + Eq> {
    data: RwLock<BiMap<AstNodeId, T>>,
}

impl<T: Hash + Eq> AstMap<T> {
    pub fn new() -> Self {
        Self { data: RwLock::new(BiMap::new()) }
    }

    pub fn insert(&self, ast_id: AstNodeId, data: T) {
        self.data.write().insert(ast_id, data);
    }
}

impl<T: Hash + Eq> Default for AstMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Hash + Eq + Copy> AstMap<T> {
    pub fn get_data_by_node(&self, ast_id: AstNodeId) -> Option<T> {
        self.data.read().get_by_left(&ast_id).copied()
    }

    pub fn get_node_by_data(&self, data: T) -> Option<AstNodeId> {
        self.data.read().get_by_right(&data).copied()
    }
}

macro_rules! ast_info {
    ($($name:ident: $ty:ty),* $(,)?) => {
        #[derive(Debug)]
        pub struct AstInfo {
            $(
                $name: $ty,
            )*
        }

        impl AstInfo {
            pub fn new() -> Self {
                Self {
                    $(
                        $name: Default::default(),
                    )*
                }
            }

            $(
                pub fn $name(&self) -> &$ty {
                    &self.$name
                }
            )*
        }

        impl Default for AstInfo {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

ast_info! {
    data_defs: AstMap<DataDefId>,
    ctor_defs: AstMap<CtorDefId>,

    mod_defs: AstMap<ModDefId>,
    mod_members: AstMap<ModMemberId>,

    fn_defs: AstMap<FnDefId>,

    stacks: AstMap<StackId>,
    stack_members: AstMap<Decl>,

    terms: AstMap<TermId>,
    tys: AstMap<TyId>,
    pats: AstMap<PatId>,

    params: AstMap<ParamId>,
    args: AstMap<ArgId>,
}
