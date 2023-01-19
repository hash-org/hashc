//! Crate that contains all of the mechanisms that are used for storing
//! information about types within the Hash type system. This crate is
//! primarily used by `hash_semantics` and `hash_lower` in order to
//! share the type representation.

use std::cell::Cell;

use hash_source::SourceId;
use hash_target::Target;
use hash_utils::store::Store;

use crate::{
    args::ArgsStore,
    bootstrap::create_core_defs_in,
    location::LocationStore,
    mods::ModDefStore,
    nodes::NodeInfoStore,
    nominals::NominalDefStore,
    params::ParamsStore,
    pats::{PatArgsStore, PatStore},
    scope::{Scope, ScopeId, ScopeKind, ScopeStack, ScopeStore},
    terms::{TermListStore, TermStore},
    trts::TrtDefStore,
};

/// Keeps track of typechecking information across all source files.
#[derive(Debug)]
pub struct GlobalStorage {
    /// Scope storage
    pub scope_store: ScopeStore,

    /// Storage for terms
    pub term_store: TermStore,

    /// Store for grouped terms
    pub term_list_store: TermListStore,

    /// Information about the locations of terms within the source
    pub location_store: LocationStore,

    /// Store for function, tuple, struct, enum and other parametrised
    /// constructs.
    pub params_store: ParamsStore,

    /// Store for function calls, tuple, struct, enum and other constructs that
    /// hold arguments.
    pub args_store: ArgsStore,

    /// Store for trait definitions
    pub trt_def_store: TrtDefStore,

    /// Store for module definitions
    pub mod_def_store: ModDefStore,

    /// Nominal definition store
    pub nominal_def_store: NominalDefStore,

    /// Store for typechecked patterns
    pub pat_store: PatStore,

    /// Store for arguments that occur in parametrised patterns such as lists,
    /// constructors and tuple patterns.
    pub pat_args_store: PatArgsStore,

    /// Map representing the relation between terms and AST nodes.
    pub node_info_store: NodeInfoStore,

    /// Used to create the first scope when creating a LocalStorage.
    ///
    /// This includes all the core language definitions; it shouldn't be
    /// directly queried, but rather the [LocalStorage] scopes should be
    /// queried.
    pub root_scope: ScopeId,

    /// The pointer width on the current target architecture.
    pub target_pointer_width: usize,
}

impl GlobalStorage {
    /// Create a new, empty [GlobalStorage].
    pub fn new(target: &Target) -> Self {
        let scope_store = ScopeStore::new();
        let root_scope = scope_store.create(Scope::empty(ScopeKind::Mod));

        let gs = Self {
            target_pointer_width: target.pointer_width,
            location_store: LocationStore::new(),
            term_store: TermStore::new(),
            term_list_store: TermListStore::new(),
            node_info_store: NodeInfoStore::new(),
            scope_store,
            trt_def_store: TrtDefStore::new(),
            mod_def_store: ModDefStore::new(),
            nominal_def_store: NominalDefStore::new(),
            pat_store: PatStore::new(),
            pat_args_store: PatArgsStore::new(),
            root_scope,
            params_store: ParamsStore::new(),
            args_store: ArgsStore::new(),
        };

        create_core_defs_in(&gs);
        gs
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
    pub fn new(gs: &GlobalStorage, id: SourceId) -> Self {
        Self {
            scopes: ScopeStack::many([
                // First the root scope
                gs.root_scope,
                // Then the scope for the source
                gs.scope_store.create(Scope::empty(ScopeKind::Mod)),
            ]),
            id: Cell::new(id),
        }
    }

    /// Get the current [SourceId]
    pub fn current_source(&self) -> SourceId {
        self.id.get()
    }

    /// Set the current [SourceId].
    pub fn set_current_source(&self, id: SourceId) {
        self.id.set(id);
    }
}

/// Storage that is used by stages that need to access type information about
/// modules in the current workspace.
#[derive(Debug)]
pub struct TyStorage {
    /// Storage that is used by the typechecker to resolve local items
    /// within certain contexts.
    pub local: LocalStorage,

    /// Persistent storage of all data structures that is emitted by the
    /// typechecking stage, and possibly further stages.
    pub global: GlobalStorage,
}
