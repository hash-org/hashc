//! Definitions related to user-defined data-types.

use core::fmt;
use std::fmt::Display;

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore, SequenceStore, SequenceStoreKey, Store},
};
use textwrap::indent;
use utility_types::omit;

use super::{
    args::{ArgsId, PatArgsId},
    environment::env::{AccessToEnv, WithEnv},
    pats::Spread,
    tys::TyId,
};
use crate::new::{params::ParamsId, symbols::Symbol};

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
    pub length: usize,
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
new_store_key!(pub DataDefId);
pub type DataDefStore = DefaultStore<DataDefId, DataDef>;

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

impl fmt::Display for WithEnv<'_, &CtorDef> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.env().with(self.value.name))?;
        if self.value.params.len() > 0 {
            write!(f, "({}) -> ", self.env().with(self.value.params))?;
        }

        let data_ty = DataTy { args: self.value.result_args, data_def: self.value.data_def_id };
        write!(f, "{}", self.env().with(&data_ty))?;

        Ok(())
    }
}

impl fmt::Display for WithEnv<'_, CtorDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().ctor_defs().map_fast(self.value.0, |ctor_defs| {
            write!(f, "{}", self.env().with(&ctor_defs[self.value.1]))
        })
    }
}

impl fmt::Display for WithEnv<'_, CtorDefsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().ctor_defs().map_fast(self.value, |ctor_defs| {
            for ctor_def in ctor_defs.iter() {
                writeln!(f, "{}", self.env().with(ctor_def))?;
            }
            Ok(())
        })
    }
}

impl Display for WithEnv<'_, &CtorTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (ctor_name, data_def_id) =
            self.stores().ctor_defs().map_fast(self.value.ctor.0, |ctors| {
                (ctors[self.value.ctor.1].name, ctors[self.value.ctor.1].data_def_id)
            });

        let data_ty = DataTy { args: self.value.data_args, data_def: data_def_id };
        write!(f, "{}::", self.env().with(&data_ty))?;

        write!(f, "{}", self.env().with(ctor_name))?;
        if self.value.ctor_args.len() > 0 {
            write!(f, "({})", self.env().with(self.value.ctor_args))?;
        }

        Ok(())
    }
}

impl Display for WithEnv<'_, &CtorPat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (ctor_name, data_def_id) =
            self.stores().ctor_defs().map_fast(self.value.ctor.0, |ctors| {
                (ctors[self.value.ctor.1].name, ctors[self.value.ctor.1].data_def_id)
            });

        let data_ty = DataTy { args: self.value.data_args, data_def: data_def_id };
        write!(f, "{}::", self.env().with(&data_ty))?;

        write!(f, "{}", self.env().with(ctor_name))?;
        if self.value.ctor_pat_args.len() > 0 || self.value.ctor_pat_args_spread.is_some() {
            write!(
                f,
                "({})",
                self.env().with((self.value.ctor_pat_args, self.value.ctor_pat_args_spread))
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

impl Display for WithEnv<'_, &PrimitiveCtorInfo> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
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
                writeln!(f, "list [{}]", self.env().with(list.element_ty))
            }
        }
    }
}

impl Display for WithEnv<'_, DataDefCtors> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            DataDefCtors::Primitive(ctor) => write!(f, "{}", self.env().with(&ctor)),
            DataDefCtors::Defined(ctors) => write!(f, "{}", self.env().with(ctors)),
        }
    }
}

impl Display for WithEnv<'_, &DataDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ctors = self.env().with(self.value.ctors).to_string();
        write!(
            f,
            "datatype [name={}] {} {{\n{}}}",
            self.env().with(self.value.name),
            if self.value.params.len() > 0 {
                format!("<{}>", self.env().with(self.value.params))
            } else {
                "".to_string()
            },
            indent(&ctors, "  ")
        )
    }
}

impl Display for WithEnv<'_, DataDefId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().data_def().map_fast(self.value, |def| write!(f, "{}", self.env().with(def)))
    }
}

impl Display for WithEnv<'_, &DataTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_def_name = self.stores().data_def().map_fast(self.value.data_def, |def| def.name);
        write!(f, "{}", self.env().with(data_def_name))?;
        if self.value.args.len() > 0 {
            write!(f, "<{}>", self.env().with(self.value.args))?;
        }
        Ok(())
    }
}
