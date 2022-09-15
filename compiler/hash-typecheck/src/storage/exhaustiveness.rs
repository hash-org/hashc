//! Stores [DeconstructedPat]s and [DeconstructedCtor]s.
use hash_utils::{new_store, new_store_key};

use crate::exhaustiveness::{construct::DeconstructedCtor, deconstruct::DeconstructedPat};

new_store_key!(pub DeconstructedPatId);
new_store!(pub DeconstructedPatStore<DeconstructedPatId, DeconstructedPat>);

new_store_key!(pub DeconstructedCtorId);
new_store!(pub DeconstructedCtorStore<DeconstructedCtorId, DeconstructedCtor>);

/// The [ExhaustivenessStorage] holds data structures that are used during
/// exhaustiveness checking as intermediate representations of patterns.
#[derive(Debug, Default)]
pub struct ExhaustivenessStorage {
    /// The [crate::exhaustiveness::deconstruct::DeconstructedPat] store.
    pub deconstructed_pat_store: DeconstructedPatStore,

    /// The [crate::exhaustiveness::construct::DeconstructedCtor] store.
    pub deconstructed_ctor_store: DeconstructedCtorStore,
}
