//! Contains structures to keep track of traits and information relating to
//! them.
use hash_utils::{new_store, new_store_key};

use crate::TrtDef;

new_store_key!(pub TrtDefId);
new_store!(pub TrtDefStore<TrtDefId, TrtDef>);
