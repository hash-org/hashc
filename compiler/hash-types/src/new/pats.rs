//! Definitions related to patterns.

use hash_utils::{new_sequence_store_key, new_store, new_store_key, store::DefaultSequenceStore};

// @@Todo
#[derive(Debug, Clone, Copy)]
pub enum Pat {}

new_sequence_store_key!(pub PatListId);
pub type PatListStore = DefaultSequenceStore<PatListId, PatId>;

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);
