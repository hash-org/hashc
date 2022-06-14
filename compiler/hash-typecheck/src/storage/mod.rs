//! Structures relating to storing type information, symbol information, and other kinds of
//! information managed by the typechecker.
//!
//! This information lives either in [LocalStorage] or [GlobalStorage], depending on if it is
//! accessible from within a given source only, or accessible globally. For example, a stack
//! variable will be in [LocalStorage] because it is only accessible from one file, whereas a
//! type definition will be in [GlobalStorage] because it can be accessed from any file (with the
//! appropriate import).

use hash_source::SourceId;

use self::{
    core::CoreDefs,
    mods::ModDefStore,
    nominals::NominalDefStore,
    scope::{Scope, ScopeStack},
    sources::CheckedSources,
    state::TypecheckState,
    trts::TrtDefStore,
    tys::TyStore,
    values::ValueStore,
};

pub mod core;
pub mod mods;
pub mod nominals;
pub mod primitives;
pub mod scope;
pub mod sources;
pub mod state;
pub mod trts;
pub mod tys;
pub mod values;

/// Keeps track of typechecking information across all source files.
pub struct GlobalStorage {
    pub ty_store: TyStore,
    pub value_store: ValueStore,
    pub trt_def_store: TrtDefStore,
    pub mod_def_store: ModDefStore,
    pub nominal_def_store: NominalDefStore,
    pub checked_sources: CheckedSources,
    pub root_scope: Scope,
}

impl GlobalStorage {
    /// Create a new, empty [GlobalStorage].
    pub fn new() -> Self {
        Self {
            ty_store: TyStore::new(),
            value_store: ValueStore::new(),
            trt_def_store: TrtDefStore::new(),
            mod_def_store: ModDefStore::new(),
            nominal_def_store: NominalDefStore::new(),
            checked_sources: CheckedSources::new(),
            root_scope: Scope::empty(scope::ScopeKind::Constant),
        }
    }
}

impl Default for GlobalStorage {
    fn default() -> Self {
        Self::new()
    }
}

/// Keeps track of typechecking information specific to a given source file.
pub struct LocalStorage {
    /// All the scopes in a given source.
    pub scopes: ScopeStack,
    /// The state of the typechecker for the given source.
    pub state: TypecheckState,
}

impl LocalStorage {
    /// Create a new, empty [LocalStorage] for the given source.
    pub fn new(source_id: SourceId) -> Self {
        Self {
            state: TypecheckState::new(source_id),
            scopes: ScopeStack::empty(),
        }
    }
}

/// A reference to the storage, which includes both local and global storage, as well as core
/// definitions.
pub struct StorageRef<'gs, 'ls, 'cd> {
    pub local_storage: &'ls LocalStorage,
    pub global_storage: &'gs GlobalStorage,
    pub core_defs: &'cd CoreDefs,
}

/// A mutable reference to the storage, which includes both local and global storage, as well as
/// core definitions.
pub struct StorageRefMut<'gs, 'ls, 'cd> {
    pub local_storage: &'ls mut LocalStorage,
    pub global_storage: &'gs mut GlobalStorage,
    pub core_defs: &'cd CoreDefs,
}

/// Trait that provides convenient accessor methods to various parts of the storage given a path to
/// a [StorageRef] object.
pub trait AccessToStorage {
    fn storages(&self) -> StorageRef;

    fn global_storage(&self) -> &GlobalStorage {
        self.storages().global_storage
    }

    fn local_storage(&self) -> &LocalStorage {
        self.storages().local_storage
    }

    fn core_defs(&mut self) -> &CoreDefs {
        self.storages().core_defs
    }

    fn ty_store(&self) -> &TyStore {
        &self.global_storage().ty_store
    }

    fn value_store(&self) -> &ValueStore {
        &self.global_storage().value_store
    }

    fn nominal_def_store(&self) -> &NominalDefStore {
        &self.global_storage().nominal_def_store
    }

    fn trt_def_store(&self) -> &TrtDefStore {
        &self.global_storage().trt_def_store
    }

    fn mod_def_store(&self) -> &ModDefStore {
        &self.global_storage().mod_def_store
    }

    fn checked_sources(&self) -> &CheckedSources {
        &self.global_storage().checked_sources
    }

    fn root_scope(&self) -> &Scope {
        &self.global_storage().root_scope
    }

    fn state(&self) -> &TypecheckState {
        &self.local_storage().state
    }

    fn scopes(&self) -> &ScopeStack {
        &self.local_storage().scopes
    }
}

/// Trait that provides convenient mutable accessor methods to various parts of the storage given a
/// path to a [StorageRefMut] object.
pub trait AccessToStorageMut: AccessToStorage {
    fn storages_mut(&mut self) -> StorageRefMut;

    fn global_storage_mut(&mut self) -> &mut GlobalStorage {
        self.storages_mut().global_storage
    }

    fn local_storage_mut(&mut self) -> &mut LocalStorage {
        self.storages_mut().local_storage
    }

    fn ty_store_mut(&mut self) -> &mut TyStore {
        &mut self.global_storage_mut().ty_store
    }

    fn value_store_mut(&mut self) -> &mut ValueStore {
        &mut self.global_storage_mut().value_store
    }

    fn nominal_def_store_mut(&mut self) -> &mut NominalDefStore {
        &mut self.global_storage_mut().nominal_def_store
    }

    fn trt_def_store_mut(&mut self) -> &mut TrtDefStore {
        &mut self.global_storage_mut().trt_def_store
    }

    fn mod_def_store_mut(&mut self) -> &mut ModDefStore {
        &mut self.global_storage_mut().mod_def_store
    }

    fn checked_sources_mut(&mut self) -> &mut CheckedSources {
        &mut self.global_storage_mut().checked_sources
    }

    fn root_scope_mut(&mut self) -> &mut Scope {
        &mut self.global_storage_mut().root_scope
    }

    fn state_mut(&mut self) -> &mut TypecheckState {
        &mut self.local_storage_mut().state
    }

    fn scopes_mut(&mut self) -> &mut ScopeStack {
        &mut self.local_storage_mut().scopes
    }
}

impl<'gs, 'ls, 'cd> AccessToStorage for StorageRef<'gs, 'ls, 'cd> {
    fn storages(&self) -> StorageRef {
        StorageRef { ..*self }
    }
}

impl<'gs, 'ls, 'cd> AccessToStorage for StorageRefMut<'gs, 'ls, 'cd> {
    fn storages(&self) -> StorageRef {
        StorageRef {
            global_storage: self.global_storage,
            local_storage: self.local_storage,
            core_defs: self.core_defs,
        }
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for StorageRefMut<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        StorageRefMut {
            global_storage: self.global_storage,
            local_storage: self.local_storage,
            core_defs: self.core_defs,
        }
    }
}
