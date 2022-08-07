//! Contains structures to keep track of nominal type definitions and
//! information relating to them.
use hash_utils::{new_store, new_store_key};

use super::primitives::NominalDef;

new_store_key!(pub NominalDefId);
new_store!(pub NominalDefStore<NominalDefId, NominalDef>);
