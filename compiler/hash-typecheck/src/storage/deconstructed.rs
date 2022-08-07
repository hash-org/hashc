//! Stores [DeconstructedPat]s and [DeconstructedCtor]s.
use hash_utils::{new_store, new_store_key};

use crate::exhaustiveness::{construct::DeconstructedCtor, deconstruct::DeconstructedPat};

new_store_key!(pub DeconstructedPatId);
new_store!(pub DeconstructedPatStore<DeconstructedPatId, DeconstructedPat>);

new_store_key!(pub DeconstructedCtorId);
new_store!(pub DeconstructedCtorStore<DeconstructedCtorId, DeconstructedCtor>);
