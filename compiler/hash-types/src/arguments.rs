//! Storage of [Arg]s
use hash_utils::new_sequence_store_key;

use crate::{param_list::ParamListStore, Arg};

new_sequence_store_key!(pub ArgsId);
pub type ArgsStore = ParamListStore<ArgsId, Arg>;
