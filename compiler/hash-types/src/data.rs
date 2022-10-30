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
pub struct CtorDef {
    pub name: Symbol,
    pub original_data_def_id: DataDefId,
    pub index: usize,
    pub params: DefParamsId,
    pub result_args: DefArgsId,
}
new_sequence_store_key!(pub CtorDefsId);
pub type CtorDefsStore = DefaultSequenceStore<CtorDefsId, CtorDef>;
pub type CtorDefId = (CtorDefsId, usize);

/// A constructor term.
#[derive(Debug, Clone, Copy)]
pub struct CtorTerm {
    pub ctor: CtorDefId,
    pub args: DefArgsId,
}

/// A data-type definition.
///
/// Includes a name, a set of parameters for the data-type, a set of
/// constructors.
#[derive(Debug, Clone, Copy)]
pub struct DataDef {
    pub name: Symbol,
    pub params: DefParamsId,
    pub ctors: CtorDefsId,
}
new_store_key!(pub DataDefId);
pub type DataDefStore = DefaultStore<DataDefId, DataDef>;

/// A type pointing to a data-type definition.
#[derive(Debug, Clone, Copy)]
pub struct DataTy {
    pub data_def: DataDefId,
    pub args: DefArgsId,
}
