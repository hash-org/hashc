//! Definitions related to user-defined data-types.

use core::fmt;
use std::fmt::Display;

use hash_utils::store::{SequenceStore, SequenceStoreKey, Store, TrivialSequenceStoreKey};
use textwrap::indent;
use utility_types::omit;

use super::{
    args::{ArgsId, PatArgsId},
    environment::stores::StoreId,
    pats::Spread,
    tys::TyId,
};
use crate::{
    params::ParamsId, pats::PatArgsWithSpread, symbols::Symbol, terms::TermId,
    tir_debug_name_of_store_id, tir_get, tir_sequence_store_direct, tir_single_store,
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
#[omit(CtorDefData, [id, data_def_id, data_def_ctor_index], [Debug, Clone, Copy])]
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
    pub params: ParamsId,
    /// The arguments given to the original data-type in the "return type" of
    /// the constructor.
    ///
    /// For example, in `Red: Color`, the `args` would be empty.
    /// In `Some: (t: T) -> Option<T>`, the `args` would be `<T>`.
    /// In `refl: (x: A) -> Id<A>(x, x)`, the `args` would be `<A>(x, x)`.
    ///
    /// This restricts the return value of each constructor to be the original
    /// data type, with some given arguments for its parameters.
    pub result_args: ArgsId,
}

tir_sequence_store_direct!(
    store = pub CtorDefsStore,
    id = pub CtorDefsId[CtorDefId],
    value = CtorDef,
    store_name = ctor_defs
);

tir_debug_name_of_store_id!(CtorDefId);

/// A constructor term.
///
/// This is an invocation of a constructor, for example `Some(3)`, which would
/// type as `Option<i32>`.
#[derive(Debug, Clone, Copy)]
pub struct CtorTerm {
    /// The constructor definition that this term is an invocation of.
    pub ctor: CtorDefId,
    /// The arguments to the data definition.
    pub data_args: ArgsId,
    /// The arguments to the constructor.
    pub ctor_args: ArgsId,
}

/// A constructor pattern.
///
/// This is a pattern matching a constructor, for example `Some(_)`.
#[derive(Debug, Clone, Copy)]
pub struct CtorPat {
    /// The constructor definition that this pattern references.
    pub ctor: CtorDefId,
    /// The pattern arguments to the constructor.
    pub ctor_pat_args: PatArgsId,
    /// The spread in the constructor members, if any.
    pub ctor_pat_args_spread: Option<Spread>,
    /// The data arguments to the constructor.
    pub data_args: ArgsId,
}

/// The number of bits in a numeric constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericCtorBits {
    /// The number of bits is bounded to the given value.
    Bounded(u8),
    /// The number of bits is unbounded (i.e. bigint).
    Unbounded,
}

/// A numeric constructor definition.
///
/// This is a constructor which accepts numeric literals
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumericCtorInfo {
    /// The number of bits in the number.
    pub bits: NumericCtorBits,
    /// Whether the number is signed or not.
    pub is_signed: bool,
    /// Whether the number is floating-point or not.
    pub is_float: bool,
    // @@Future: allowable range?
}

/// An array constructor definition.
/// This is a constructor which accepts array literals.
#[derive(Debug, Clone, Copy)]
pub struct ArrayCtorInfo {
    /// The type of the elements in the array.
    pub element_ty: TyId,

    /// The number of elements in the array.
    pub length: Option<TermId>,
}

/// A primitive constructor definition.
///
/// This is a constructor which accepts a primitive literal.
#[derive(Debug, Clone, Copy)]
pub enum PrimitiveCtorInfo {
    /// A numeric literal constructor.
    Numeric(NumericCtorInfo),
    /// A string literal constructor.
    Str,
    /// A character literal constructor.
    Char,
    /// A list literal constructor.
    Array(ArrayCtorInfo),
}

/// The constructors of a data-type definition.
///
/// These are either a given set of predefined constructors, or a primitive
/// constructor (numeric, string, character).
#[derive(Debug, Clone, Copy)]
pub enum DataDefCtors {
    Defined(CtorDefsId),
    Primitive(PrimitiveCtorInfo),
}

impl DataDefCtors {
    /// Assert that the [DataDefCtors] is non-primitive.
    pub fn assert_defined(self) -> CtorDefsId {
        match self {
            DataDefCtors::Defined(ctors) => ctors,
            DataDefCtors::Primitive(_) => panic!("expected defined data type"),
        }
    }
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
    /// For example `<A: Type>` in `Bingo := datatype <A: Type> (x:
    /// i32)`.
    pub params: ParamsId,
    /// The ordered list of constructors for the data-type.
    ///
    /// This list is ordered so that a constructor can refer back to its
    /// location in this list using a `usize` index.
    pub ctors: DataDefCtors,
}

tir_single_store!(
    store = pub DataDefStore,
    id = pub DataDefId,
    value = DataDef,
    store_name = data_def
);

tir_debug_name_of_store_id!(DataDefId);

/// A type pointing to a data-type definition.
///
/// This is, for example `Option<i32>` when it is used in type position `y:
/// Option<i32>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DataTy {
    /// The data-type definition of this type.
    pub data_def: DataDefId,

    /// The arguments to the data-type definition.
    pub args: ArgsId,
}

impl fmt::Display for CtorDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.name)?;
        if self.params.len() > 0 {
            write!(f, "({}) -> ", self.params)?;
        }

        let data_ty = DataTy { args: self.result_args, data_def: self.data_def_id };
        write!(f, "{}", &data_ty)?;

        Ok(())
    }
}

impl fmt::Display for CtorDefId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for CtorDefsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for ctor_def in self.iter() {
            writeln!(f, "{}", ctor_def)?;
        }
        Ok(())
    }
}

impl Display for CtorTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (ctor_name, data_def_id) =
            (tir_get!(self.ctor, name), tir_get!(self.ctor, data_def_id));

        let data_ty = DataTy { args: self.data_args, data_def: data_def_id };
        write!(f, "{}::", &data_ty)?;

        write!(f, "{}", ctor_name)?;
        if self.ctor_args.len() > 0 {
            write!(f, "({})", self.ctor_args)?;
        }

        Ok(())
    }
}

impl Display for CtorPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (ctor_name, data_def_id) =
            (tir_get!(self.ctor, name), tir_get!(self.ctor, data_def_id));

        let data_ty = DataTy { args: self.data_args, data_def: data_def_id };
        write!(f, "{}::", &data_ty)?;

        write!(f, "{}", ctor_name)?;
        if self.ctor_pat_args.len() > 0 || self.ctor_pat_args_spread.is_some() {
            write!(
                f,
                "({})",
                PatArgsWithSpread {
                    pat_args: self.ctor_pat_args,
                    spread: self.ctor_pat_args_spread
                }
            )?;
        }

        Ok(())
    }
}

impl Display for NumericCtorBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NumericCtorBits::Bounded(bits) => write!(f, "{bits}"),
            NumericCtorBits::Unbounded => write!(f, "unbounded"),
        }
    }
}

impl Display for PrimitiveCtorInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveCtorInfo::Numeric(numeric) => {
                writeln!(
                    f,
                    "numeric [bits={}, float={}, signed={}]",
                    numeric.bits, numeric.is_float, numeric.is_signed,
                )
            }
            PrimitiveCtorInfo::Str => {
                writeln!(f, "str")
            }
            PrimitiveCtorInfo::Char => {
                writeln!(f, "char")
            }
            PrimitiveCtorInfo::Array(list) => {
                writeln!(f, "list [{}]", list.element_ty)
            }
        }
    }
}

impl Display for DataDefCtors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataDefCtors::Primitive(ctor) => write!(f, "{}", &ctor),
            DataDefCtors::Defined(ctors) => write!(f, "{}", ctors),
        }
    }
}

impl Display for DataDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ctors = (self.ctors).to_string();
        write!(
            f,
            "datatype [name={}] {} {{\n{}}}",
            self.name,
            if self.params.len() > 0 { format!("<{}>", self.params) } else { "".to_string() },
            indent(&ctors, "  ")
        )
    }
}

impl Display for DataDefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl Display for DataTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_def_name = tir_get!(self.data_def, name);
        write!(f, "{}", data_def_name)?;
        if self.args.len() > 0 {
            write!(f, "<{}>", self.args)?;
        }
        Ok(())
    }
}
