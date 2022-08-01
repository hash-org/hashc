//! Structures relating to storing type information, symbol information, and
//! other kinds of information managed by the typechecker.
//!
//! This information lives either in [LocalStorage] or [GlobalStorage],
//! depending on if it is accessible from within a given source only, or
//! accessible globally. For example, a stack variable will be in [LocalStorage]
//! because it is only accessible from one file, whereas a type definition will
//! be in [GlobalStorage] because it can be accessed from any file (with the
//! appropriate import).
use std::cell::Cell;

use hash_source::{SourceId, SourceMap};

use crate::fmt::{ForFormatting, PrepareForFormatting};

use self::{
    arguments::ArgsStore,
    cache::Cache,
    core::CoreDefs,
    location::LocationStore,
    mods::ModDefStore,
    nominals::NominalDefStore,
    params::ParamsStore,
    pats::{PatArgsStore, PatStore},
    primitives::{Scope, ScopeId, ScopeKind},
    scope::{ScopeStack, ScopeStore},
    sources::CheckedSources,
    terms::TermStore,
    trts::TrtDefStore,
};

pub mod arguments;
pub mod cache;
pub mod core;
pub mod location;
pub mod mods;
pub mod nominals;
pub mod params;
pub mod pats;
pub mod primitives;
pub mod scope;
pub mod sources;
pub mod terms;
pub mod trts;

/// Keeps track of typechecking information across all source files.
#[derive(Debug)]
pub struct GlobalStorage {
    pub scope_store: ScopeStore,
    pub term_store: TermStore,
    pub location_store: LocationStore,
    pub params_store: ParamsStore,
    pub args_store: ArgsStore,
    pub trt_def_store: TrtDefStore,
    pub mod_def_store: ModDefStore,
    pub nominal_def_store: NominalDefStore,
    pub pat_store: PatStore,
    pub pat_args_store: PatArgsStore,
    pub checked_sources: CheckedSources,

    /// The typechecking cache, contains cached simplification, validation
    /// and unification results
    pub cache: Cache,

    /// Used to create the first scope when creating a LocalStorage.
    ///
    /// This includes all the core language definitions; it shouldn't be
    /// directly queried, but rather the [LocalStorage] scopes should be
    /// queried.
    pub root_scope: ScopeId,
}

impl GlobalStorage {
    /// Create a new, empty [GlobalStorage].
    pub fn new() -> Self {
        let mut scope_store = ScopeStore::new();
        let root_scope = scope_store.create(Scope::empty(ScopeKind::Constant));
        Self {
            location_store: LocationStore::new(),
            term_store: TermStore::new(),
            scope_store,
            trt_def_store: TrtDefStore::new(),
            mod_def_store: ModDefStore::new(),
            nominal_def_store: NominalDefStore::new(),
            pat_store: PatStore::new(),
            pat_args_store: PatArgsStore::new(),
            checked_sources: CheckedSources::new(),
            root_scope,
            params_store: ParamsStore::new(),
            args_store: ArgsStore::new(),
            cache: Cache::new(),
        }
    }
}

impl Default for GlobalStorage {
    fn default() -> Self {
        Self::new()
    }
}

/// Keeps track of typechecking information specific to a given source file.
#[derive(Debug)]
pub struct LocalStorage {
    /// All the scopes in a given source.
    pub scopes: ScopeStack,
    /// The current [SourceId]
    pub id: Cell<SourceId>,
}

impl LocalStorage {
    /// Create a new, empty [LocalStorage] for the given source.
    pub fn new(gs: &mut GlobalStorage, id: SourceId) -> Self {
        Self {
            scopes: ScopeStack::many([
                // First the root scope
                gs.root_scope,
                // Then the scope for the source
                gs.scope_store.create(Scope::empty(ScopeKind::Constant)),
            ]),
            id: Cell::new(id),
        }
    }

    /// Get the current [SourceId]
    pub fn current_source(&self) -> SourceId {
        self.id.get()
    }

    /// Set the current [SourceId], it does not matter whether
    /// this is a [SourceId::Module] or [SourceId::Interactive]
    pub fn set_current_source(&mut self, id: SourceId) {
        self.id.set(id);
    }
}

/// A reference to the storage, which includes both local and global storage, as
/// well as core definitions.
#[derive(Debug, Clone, Copy)]
pub struct StorageRef<'gs, 'ls, 'cd, 's> {
    pub local_storage: &'ls LocalStorage,
    pub global_storage: &'gs GlobalStorage,
    pub core_defs: &'cd CoreDefs,
    source_map: &'s SourceMap,
}

/// A mutable reference to the storage, which includes both local and global
/// storage, as well as core definitions.
#[derive(Debug)]
pub struct StorageRefMut<'gs, 'ls, 'cd, 's> {
    pub local_storage: &'ls mut LocalStorage,
    pub global_storage: &'gs mut GlobalStorage,
    pub core_defs: &'cd CoreDefs,
    pub source_map: &'s SourceMap,
}

/// Trait that provides convenient accessor methods to various parts of the
/// storage given a path to a [StorageRef] object.
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

    fn scope_store(&self) -> &ScopeStore {
        &self.global_storage().scope_store
    }

    fn term_store(&self) -> &TermStore {
        &self.global_storage().term_store
    }

    fn cache(&self) -> &Cache {
        &self.global_storage().cache
    }

    fn location_store(&self) -> &LocationStore {
        &self.global_storage().location_store
    }

    fn nominal_def_store(&self) -> &NominalDefStore {
        &self.global_storage().nominal_def_store
    }

    fn trt_def_store(&self) -> &TrtDefStore {
        &self.global_storage().trt_def_store
    }

    fn args_store(&self) -> &ArgsStore {
        &self.global_storage().args_store
    }

    fn params_store(&self) -> &ParamsStore {
        &self.global_storage().params_store
    }

    fn mod_def_store(&self) -> &ModDefStore {
        &self.global_storage().mod_def_store
    }

    fn pat_store(&self) -> &PatStore {
        &self.global_storage().pat_store
    }

    fn pat_params_store(&self) -> &PatArgsStore {
        &self.global_storage().pat_args_store
    }

    fn checked_sources(&self) -> &CheckedSources {
        &self.global_storage().checked_sources
    }

    fn root_scope(&self) -> ScopeId {
        self.global_storage().root_scope
    }

    fn scopes(&self) -> &ScopeStack {
        &self.local_storage().scopes
    }

    /// Create a [ForFormatting] for the given `T` and [GlobalStorage] from
    /// self.
    fn for_fmt<T>(&self, t: T) -> ForFormatting<T>
    where
        T: PrepareForFormatting,
    {
        t.for_formatting(self.global_storage())
    }

    /// Get a reference to the [SourceMap]
    fn source_map(&self) -> &SourceMap {
        self.storages().source_map
    }
}

/// Trait that provides convenient mutable accessor methods to various parts of
/// the storage given a path to a [StorageRefMut] object.
pub trait AccessToStorageMut: AccessToStorage {
    fn storages_mut(&mut self) -> StorageRefMut;

    fn global_storage_mut(&mut self) -> &mut GlobalStorage {
        self.storages_mut().global_storage
    }

    fn local_storage_mut(&mut self) -> &mut LocalStorage {
        self.storages_mut().local_storage
    }

    fn term_store_mut(&mut self) -> &mut TermStore {
        &mut self.global_storage_mut().term_store
    }

    fn cache_mut(&mut self) -> &mut Cache {
        &mut self.global_storage_mut().cache
    }

    fn location_store_mut(&mut self) -> &mut LocationStore {
        &mut self.global_storage_mut().location_store
    }

    fn scope_store_mut(&mut self) -> &mut ScopeStore {
        &mut self.global_storage_mut().scope_store
    }

    fn nominal_def_store_mut(&mut self) -> &mut NominalDefStore {
        &mut self.global_storage_mut().nominal_def_store
    }

    fn trt_def_store_mut(&mut self) -> &mut TrtDefStore {
        &mut self.global_storage_mut().trt_def_store
    }

    fn args_store_mut(&mut self) -> &mut ArgsStore {
        &mut self.global_storage_mut().args_store
    }

    fn params_store_mut(&mut self) -> &mut ParamsStore {
        &mut self.global_storage_mut().params_store
    }

    fn mod_def_store_mut(&mut self) -> &mut ModDefStore {
        &mut self.global_storage_mut().mod_def_store
    }

    fn pat_store_mut(&mut self) -> &mut PatStore {
        &mut self.global_storage_mut().pat_store
    }

    fn pat_params_store_mut(&mut self) -> &mut PatArgsStore {
        &mut self.global_storage_mut().pat_args_store
    }

    fn checked_sources_mut(&mut self) -> &mut CheckedSources {
        &mut self.global_storage_mut().checked_sources
    }

    fn scopes_mut(&mut self) -> &mut ScopeStack {
        &mut self.local_storage_mut().scopes
    }
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for StorageRef<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        StorageRef { ..*self }
    }
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for StorageRefMut<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        StorageRef {
            global_storage: self.global_storage,
            local_storage: self.local_storage,
            core_defs: self.core_defs,
            source_map: self.source_map,
        }
    }
}

impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for StorageRefMut<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        StorageRefMut {
            global_storage: self.global_storage,
            local_storage: self.local_storage,
            core_defs: self.core_defs,
            source_map: self.source_map,
        }
    }
}
