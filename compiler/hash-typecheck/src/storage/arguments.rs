//! Storage of [Arg]s
use hash_utils::new_sequence_store_key;

use super::{param_list::ParamListStore, primitives::Arg};

new_sequence_store_key!(pub ArgsId);
pub type ArgsStore = ParamListStore<ArgsId, Arg>;
