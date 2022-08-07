//! Storage of [Param]s
use hash_utils::new_sequence_store_key;

use super::{param_list::ParamListStore, primitives::Param};

new_sequence_store_key!(pub ParamsId);
pub type ParamsStore = ParamListStore<ParamsId, Param>;
