//! Contains structures to keep track of modules and information relating to
//! them.
use hash_utils::{new_store, new_store_key};

use crate::ModDef;

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);
