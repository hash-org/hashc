use hash_utils::{new_sequence_store, new_sequence_store_key, new_store, new_store_key};

use super::primitives::{Scope, Term};

new_store_key!(pub ScopeId);
new_store!(pub ScopeStore<ScopeId, Scope>);

new_store_key!(pub TermId);
new_store!(pub TermStore<TermId, Term>);

new_sequence_store_key!(pub TermListId);
new_sequence_store!(pub TermListStore<TermListId, Term>);

/// Keeps track of typechecking information across all source files.
#[derive(Debug)]
pub struct GlobalStorage {
    pub scope_store: ScopeStore,
    // pub term_store: TermStore,
    // pub location_store: LocationStore,
    // pub params_store: ParamsStore,
    // pub args_store: ArgsStore,
    // pub trt_def_store: TrtDefStore,
    // pub mod_def_store: ModDefStore,
    // pub nominal_def_store: NominalDefStore,
    // pub pat_store: PatStore,
    // pub pat_args_store: PatArgsStore,
    // pub checked_sources: CheckedSources,

    // /// The typechecking cache, contains cached simplification, validation
    // /// and unification results
    // pub cache: Cache,

    // /// Used to create the first scope when creating a LocalStorage.
    // ///
    // /// This includes all the core language definitions; it shouldn't be
    // /// directly queried, but rather the [LocalStorage] scopes should be
    // /// queried.
    // pub root_scope: ScopeId,
}
