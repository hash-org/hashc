//! Stores [DeconstructedPat]s and [DeconstructedCtor]s.
use crate::exhaustiveness::{construct::DeconstructedCtor, deconstruct::DeconstructedPat};
use hash_utils::{new_store, new_store_key};

new_store_key!(pub DeconstructedPatId);
new_store!(pub DeconstructedPatStore<DeconstructedPatId, DeconstructedPat>);

new_store_key!(pub DeconstructedCtorId);
new_store!(pub DeconstructedCtorStore<DeconstructedCtorId, DeconstructedCtor>);
