//! Storage of [Arg]s
use super::{param_list::ParamListStore, primitives::Arg};
use hash_utils::new_sequence_store_key;

new_sequence_store_key!(pub ArgsId);
pub type ArgsStore = ParamListStore<ArgsId, Arg>;
