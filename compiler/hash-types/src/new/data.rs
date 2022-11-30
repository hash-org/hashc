//! Definitions related to user-defined data-types.

use std::fmt::Display;

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore},
};
use utility_types::omit;

use super::{defs::DefPatArgsId, environment::env::WithEnv};
use crate::new::{
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
#[derive(Debug, Copy, Clone)]
#[omit(CtorDefData, [id], [Debug, Clone, Copy])]
pub struct CtorDef {
    /// The ID of the constructor.
    pub id: CtorDefId,
    /// The name of the constructor, for example `symbol("Red")` in `Red: Color`
    /// if given as a constructor to a `Colour := datatype...`.
    pub name: Symbol,
    /// The `DataDefId` of the data-type that this constructor is a part of.
    pub data_def_id: DataDefId,
    /// The index of this constructor in the original data-type's ordered
    /// constructor list (`ctors`).
    pub data_def_ctor_index: usize,
    /// The parameters of the constructor.
    // @@Todo: formalise positivity requirements
    pub params: DefParamsId,
    /// The arguments given to the original data-type in the "return type" of
    /// the constructor.
    ///
    /// For example, in `Red: Color`, the `args` would be empty.
    /// In `Some: (t: T) -> Option<T>`, the `args` would be `<T>`.
    /// In `refl: (x: A) -> Id<A>(x, x)`, the `args` would be `<A>(x, x)`.
    ///
    /// This restricts the return value of each constructor to be the original
    /// data type, with some given arguments for its parameters.
    pub result_args: DefArgsId,
}
new_sequence_store_key!(pub CtorDefsId);
pub type CtorDefsStore = DefaultSequenceStore<CtorDefsId, CtorDef>;
pub type CtorDefId = (CtorDefsId, usize);

/// A constructor term.
///
/// This is an invocation of a constructor, for example `Some(3)`, which would
/// type as `Option<i32>`.
#[derive(Debug, Clone, Copy)]
pub struct CtorTerm {
    /// The constructor definition that this term is an invocation of.
    pub ctor: CtorDefId,
    /// The arguments to the constructor.
    pub args: DefArgsId,
}

/// A constructor pattern.
///
/// This is a pattern matching a constructor, for example `Some(_)`.
#[derive(Debug, Clone, Copy)]
pub struct CtorPat {
    /// The constructor definition that this pattern references.
    pub ctor: CtorDefId,
    /// The pattern arguments to the constructor.
    pub args: DefPatArgsId,
}

/// A data-type definition.
///
/// This is a "nominal" inductively defined data type, which is how user-defined
/// data types in Hash are done. It consists of a set of constructors, each of
/// which provide a different way to construct the data type.
#[omit(DataDefData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct DataDef {
    /// The ID of the data-type definition.
    pub id: DataDefId,
    /// The name of the data-type.
    ///
    /// For example `symbol("Colour")` in `Colour := datatype...`.
    pub name: Symbol,
    /// The parameters of the data-type.
    ///
    /// For example `<A: Type>(x: i32)` in `Bingo := datatype <A: Type> (x:
    /// i32)`.
    pub params: DefParamsId,
    /// The ordered list of constructors for the data-type.
    ///
    /// This list is ordered so that a constructor can refer back to its
    /// location in this list using a `usize` index.
    pub ctors: CtorDefsId,
}
new_store_key!(pub DataDefId);
pub type DataDefStore = DefaultStore<DataDefId, DataDef>;

/// A type pointing to a data-type definition.
///
/// This is, for example `Option<i32>` when it is used in type position `y:
/// Option<i32>`.
#[derive(Debug, Clone, Copy)]
pub struct DataTy {
    /// The data-type definition of this type.
    pub data_def: DataDefId,
    /// The arguments to the data-type definition.
    pub args: DefArgsId,
}

impl Display for WithEnv<'_, &DataTy> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Display for WithEnv<'_, DataDefId> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Display for WithEnv<'_, &DataDef> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
