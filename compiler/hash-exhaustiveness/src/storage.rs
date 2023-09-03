//! Stores [DeconstructedPat]s and [DeconstructedCtor]s.'
use hash_storage::{new_store_key, store::DefaultStore};

use crate::{construct::DeconstructedCtor, deconstruct::DeconstructedPat};

new_store_key!(pub DeconstructedPatId, derives = Debug);
pub type DeconstructedPatStore = DefaultStore<DeconstructedPatId, DeconstructedPat>;

new_store_key!(pub DeconstructedCtorId, derives = Debug);
pub type DeconstructedCtorStore = DefaultStore<DeconstructedCtorId, DeconstructedCtor>;

/// The [ExhaustivenessStorage] holds data structures that are used during
/// exhaustiveness checking as intermediate representations of patterns.
#[derive(Debug, Default)]
pub struct ExhaustivenessCtx {
    /// The [crate::deconstruct::DeconstructedPat] store.
    pub deconstructed_pat_store: DeconstructedPatStore,

    /// The [crate::construct::DeconstructedCtor] store.
    pub deconstructed_ctor_store: DeconstructedCtorStore,
}

impl ExhaustivenessCtx {
    /// Create a new [ExhaustivenessCtx].
    pub fn new() -> Self {
        Self {
            deconstructed_ctor_store: DefaultStore::new(),
            deconstructed_pat_store: DefaultStore::new(),
        }
    }
}
