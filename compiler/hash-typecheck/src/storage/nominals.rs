//! Contains structures to keep track of nominal type definitions and
//! information relating to them.
use super::primitives::NominalDef;
use hash_utils::{new_store, new_store_key};

new_store_key!(pub NominalDefId);
new_store!(pub NominalDefStore<NominalDefId, NominalDef>);
