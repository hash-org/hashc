use std::{collections::HashMap, fmt::Debug, hash::Hash};

use hash_ast::ast::AstNodeId;
use hash_storage::store::FxHashMap;
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

/// This is used to store the relations between [AstNodeId]s and their
/// respective [`T`]. There is no assumption that the relation is uniquely
/// biderctional, e.g. multiple function definitions may point to one
/// [AstNodeId], i.e. mono-morphization.
#[derive(Debug, Default)]
struct AstMapInner<T: Hash + Eq + Copy> {
    left: FxHashMap<AstNodeId, T>,
    right: HashMap<T, AstNodeId>,
}

impl<T: Hash + Eq + Copy> AstMapInner<T> {
    /// A new empty map.
    pub fn new() -> Self {
        Self { left: FxHashMap::default(), right: HashMap::default() }
    }

    /// Perform an insertion.
    pub fn insert(&mut self, key: AstNodeId, value: T) {
        self.left.insert(key, value);
        self.right.insert(value, key);
    }

    /// Insert a key only into the right map.
    pub fn insert_right(&mut self, key: T, value: AstNodeId) {
        self.right.insert(key, value);
    }

    /// Get the value by left associatation, i.e. by [AstNodeId]. This
    /// will return the first item that was registered to the [AstNodeId].
    pub fn get_by_left(&self, key: AstNodeId) -> Option<T> {
        self.left.get(&key).copied()
    }

    /// Get the value by right association, i.e. by [`T`].
    pub fn get_by_right(&self, key: &T) -> Option<AstNodeId> {
        self.right.get(key).copied()
    }
}

/// A partial mapping from AST nodes to `T` and back.
#[derive(Debug)]
pub struct AstMap<T: Hash + Eq + Copy> {
    data: RwLock<AstMapInner<T>>,
}

impl<T: Hash + Eq + Copy> AstMap<T> {
    pub fn new() -> Self {
        Self { data: RwLock::new(AstMapInner::new()) }
    }

    pub fn insert(&self, ast_id: AstNodeId, data: T) {
        self.data.write().insert(ast_id, data);
    }
}

impl<T: Hash + Eq + Copy> Default for AstMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Hash + Eq + Copy> AstMap<T> {
    pub fn get_data_by_node(&self, ast_id: AstNodeId) -> Option<T> {
        self.data.read().get_by_left(ast_id)
    }

    pub fn get_node_by_data(&self, data: T) -> Option<AstNodeId> {
        self.data.read().get_by_right(&data)
    }

    /// This will copy the node from `src` to `dest`. This is useful for
    /// when we want to copy over [AstNodeId] reference from the source
    /// to destination. If the `src` does not have a [AstNodeId] associated
    /// with it, then this will do nothing.
    pub fn copy_node(&self, src: T, dest: T) {
        if src == dest {
            return;
        }

        let old_data = { self.data.read().get_by_right(&src) };

        if let Some(ast_id) = old_data {
            self.data.write().insert_right(dest, ast_id);
        }
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
