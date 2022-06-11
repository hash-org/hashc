//! Structures relating to storing type information, symbol information, and other kinds of
//! information managed by the typechecker.
//!
//! This information lives either in [LocalStorage] or [GlobalStorage], depending on if it is
//! accessible from within a given source only, or accessible globally. For example, a stack
//! variable will be in [LocalStorage] because it is only accessible from one file, whereas a
//! type definition will be in [GlobalStorage] because it can be accessed from any file (with the
//! appropriate import).

use self::{tys::TyStore, trts::TrtDefStore, mods::ModDefStore, sources::CheckedSources, core::CoreDefs, nominals::NominalDefStore, scope::Scope};
pub mod core;
pub mod mods;
pub mod nominals;
pub mod primitives;
pub mod sources;
pub mod tys;
pub mod trts;
pub mod scope;


pub struct GlobalStorage {
    pub ty_store: TyStore,
    pub trt_def_store: TrtDefStore,
    pub mod_def_store: ModDefStore,
    pub nominal_def_store: NominalDefStore,
    pub checked_sources: CheckedSources,
    pub core_defs: CoreDefs,
    pub root_scope: Scope,
}

// @@TODO: LocalStorage, GlobalStorage, Reference types for accessing them
