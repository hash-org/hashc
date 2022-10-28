//! Structures relating to storing type information, symbol information, and
//! other kinds of information managed by the typechecker.
//!
//! This information lives either in [LocalStorage] or [GlobalStorage],
//! depending on if it is accessible from within a given source only, or
//! accessible globally. For example, a stack variable will be in [LocalStorage]
//! because it is only accessible from one file, whereas a type definition will
//! be in [GlobalStorage] because it can be accessed from any file (with the
//! appropriate import).

pub mod cache;
pub mod exhaustiveness;
pub mod sources;

use hash_source::SourceMap;
use hash_types::{
    arguments::ArgsStore,
    fmt::{ForFormatting, PrepareForFormatting},
    location::LocationStore,
    mods::ModDefStoreOld,
    nodes::NodeInfoStore,
    nominals::NominalDefStore,
    params::ParamsStore,
    pats::{PatArgsStore, PatStore},
    scope::{ScopeId, ScopeStack, ScopeStore},
    storage::{GlobalStorage, LocalStorage},
    terms::{TermListStore, TermStore},
    trts::TrtDefStoreOld,
};

use self::{
    cache::Cache,
    exhaustiveness::{DeconstructedCtorStore, DeconstructedPatStore, ExhaustivenessStorage},
    sources::CheckedSources,
};
use crate::diagnostics::DiagnosticsStore;

/// A reference to the storage, which includes both local and global storage, as
/// well as core definitions.
#[derive(Debug, Clone, Copy)]
pub struct StorageRef<'tc> {
    /// Map containing about which source have been typechecked.
    pub checked_sources: &'tc CheckedSources,

    pub local_storage: &'tc LocalStorage,
    pub global_storage: &'tc GlobalStorage,

    /// Data stored for exhaustiveness checking
    pub exhaustiveness_storage: &'tc ExhaustivenessStorage,

    /// Current session sourcemap
    pub source_map: &'tc SourceMap,
    /// Storage for tc diagnostics.
    pub diagnostics_store: &'tc DiagnosticsStore,

    /// The typechecking cache, contains cached simplification, validation
    /// and unification results.
    pub cache: &'tc Cache,
}

/// Trait that provides convenient accessor methods to various parts of the
/// storage given a path to a [StorageRef] object.
pub trait AccessToStorage {
    fn storages(&self) -> StorageRef;

    fn global_storage(&self) -> &GlobalStorage {
        self.storages().global_storage
    }

    fn exhaustiveness_storage(&self) -> &ExhaustivenessStorage {
        self.storages().exhaustiveness_storage
    }

    fn local_storage(&self) -> &LocalStorage {
        self.storages().local_storage
    }

    fn diagnostic_store(&self) -> &DiagnosticsStore {
        self.storages().diagnostics_store
    }

    fn scope_store(&self) -> &ScopeStore {
        &self.global_storage().scope_store
    }

    fn term_store(&self) -> &TermStore {
        &self.global_storage().term_store
    }

    fn term_list_store(&self) -> &TermListStore {
        &self.global_storage().term_list_store
    }

    fn node_info_store(&self) -> &NodeInfoStore {
        &self.global_storage().node_info_store
    }

    fn cache(&self) -> &Cache {
        self.storages().cache
    }

    fn location_store(&self) -> &LocationStore {
        &self.global_storage().location_store
    }

    fn nominal_def_store(&self) -> &NominalDefStore {
        &self.global_storage().nominal_def_store
    }

    fn trt_def_store(&self) -> &TrtDefStoreOld {
        &self.global_storage().trt_def_store
    }

    fn args_store(&self) -> &ArgsStore {
        &self.global_storage().args_store
    }

    fn params_store(&self) -> &ParamsStore {
        &self.global_storage().params_store
    }

    fn mod_def_store(&self) -> &ModDefStoreOld {
        &self.global_storage().mod_def_store
    }

    fn pat_store(&self) -> &PatStore {
        &self.global_storage().pat_store
    }

    fn constructor_store(&self) -> &DeconstructedCtorStore {
        &self.exhaustiveness_storage().deconstructed_ctor_store
    }

    fn deconstructed_pat_store(&self) -> &DeconstructedPatStore {
        &self.exhaustiveness_storage().deconstructed_pat_store
    }

    fn pat_args_store(&self) -> &PatArgsStore {
        &self.global_storage().pat_args_store
    }

    fn checked_sources(&self) -> &CheckedSources {
        self.storages().checked_sources
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

impl<'tc> AccessToStorage for StorageRef<'tc> {
    fn storages(&self) -> StorageRef {
        StorageRef { ..*self }
    }
}
