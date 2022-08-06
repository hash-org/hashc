//! Contains structures to keep track of traits and information relating to
//! them.
use super::primitives::TrtDef;
use hash_utils::{new_store, new_store_key};

new_store_key!(pub TrtDefId);
new_store!(pub TrtDefStore<TrtDefId, TrtDef>);
