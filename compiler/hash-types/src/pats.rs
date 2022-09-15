//! Contains structures to keep track of patterns and information relating to
//! them.
use hash_utils::{new_sequence_store_key, new_store, new_store_key};

use crate::{param_list::ParamListStore, Pat, PatArg};

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

new_sequence_store_key!(pub PatArgsId);
pub type PatArgsStore = ParamListStore<PatArgsId, PatArg>;