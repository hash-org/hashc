//! Storage of [Param]s
use super::{param_list::ParamListStore, primitives::Param};
use hash_utils::new_sequence_store_key;

new_sequence_store_key!(pub ParamsId);
pub type ParamsStore = ParamListStore<ParamsId, Param>;
