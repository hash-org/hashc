//! Contains structures to keep track of modules and information relating to
//! them.
use hash_utils::{new_store, new_store_key};

use super::primitives::TyFnDef;

new_store_key!(pub TyFnDefId);
new_store!(pub TyFnDefStore<TyFnDefId, TyFnDef>);
