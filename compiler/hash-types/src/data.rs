//! Definitions related to user-defined data-types.

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore},
};

use crate::{
    defs::{DefArgsId, DefParamsId},
    symbols::Symbol,
};

/// A constructor of a data-type definition.
///
/// Includes a name, the original data-type definition, an index into the
/// original data-type's constructor list, a set of parameters for the
/// constructor.
///
/// Each constructor must result in the original data-type, with some given
/// arguments.
#[derive(Debug, Clone, Copy)]
pub struct Ctor {
    pub name: Symbol,
    pub data_def: DataDefId,
    pub index: usize,
    pub params: DefParamsId,
    pub result_args: DefArgsId,
}
new_sequence_store_key!(pub CtorsId);
pub type CtorsStore = DefaultSequenceStore<CtorsId, Ctor>;

/// A data-type definition.
///
/// Includes a name, a set of parameters for the data-type, a set of
/// constructors.
#[derive(Debug, Clone, Copy)]
pub struct DataDef {
    pub name: Symbol,
    pub params: DefParamsId,
    pub ctors: CtorsId,
}
new_store_key!(pub DataDefId);
pub type DataDefStore = DefaultStore<DataDefId, DataDef>;
