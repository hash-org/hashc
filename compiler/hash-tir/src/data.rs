//! Definitions related to user-defined data-types.

use core::fmt;
use std::{borrow::Borrow, fmt::Display, iter::once};

use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    SequenceStore, SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::itertools::Itertools;
use textwrap::indent;
use utility_types::omit;

use super::{
    args::{ArgsId, PatArgsId},
    pats::Spread,
    tys::TyId,
};
use crate::{
    args::Arg,
    environment::stores::tir_stores,
    node::{Node, NodeOrigin},
    params::{Param, ParamsId},
    pats::PatArgsWithSpread,
    symbols::Symbol,
    terms::TermId,
    tir_get, tir_node_sequence_store_direct, tir_node_single_store,
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

tir_node_sequence_store_direct!(
    store = pub (CtorDefsStore -> CtorDefsSeqStore),
    id = pub (CtorDefsId -> CtorDefsSeqId)[CtorDefId],
    value = CtorDef,
    store_name = (ctor_defs, ctor_defs_seq)
);

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

impl CtorDef {
    /// Create data constructors from the given iterator, for the given data
    /// definition.
    pub fn seq_from_data<I: IntoIterator<Item = CtorDefData>>(
        data_def_id: DataDefId,
        data: I,
    ) -> CtorDefsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        Node::create(Node::at(
            Node::seq_data(data.into_iter().enumerate().map(|(index, data)| {
                Node::at(
                    CtorDef {
                        name: data.name,
                        data_def_id,
                        data_def_ctor_index: index,
                        params: data.params,
                        result_args: data.result_args,
                    },
                    NodeOrigin::Generated,
                )
            })),
            NodeOrigin::Generated,
        ))
    }
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

tir_node_single_store!(
    store = pub DataDefStore,
    id = pub DataDefId,
    value = DataDef,
    store_name = data_def
);

impl DataDef {
    /// Create an empty data definition.
    pub fn empty(name: Symbol, params: ParamsId) -> DataDefId {
        Node::create_at(
            DataDef {
                name,
                params,
                ctors: DataDefCtors::Defined(Node::create(Node::at(
                    Node::<CtorDef>::empty_seq(),
                    NodeOrigin::Generated,
                ))),
            },
            NodeOrigin::Generated,
        )
    }

    /// Create a primitive data definition.
    pub fn primitive(name: Symbol, info: PrimitiveCtorInfo) -> DataDefId {
        Node::create_at(
            DataDef {
                name,
                params: Node::create(Node::at(Node::<Param>::empty_seq(), NodeOrigin::Generated)),
                ctors: DataDefCtors::Primitive(info),
            },
            NodeOrigin::Generated,
        )
    }

    /// Create a primitive data definition with parameters.
    ///
    /// These may be referenced in `info`.
    pub fn primitive_with_params(
        name: Symbol,
        params: ParamsId,
        info: impl FnOnce(DataDefId) -> PrimitiveCtorInfo,
    ) -> DataDefId {
        Node::create_with(|id| {
            Node::at(
                DataDef { name, params, ctors: DataDefCtors::Primitive(info(id)) },
                NodeOrigin::Generated,
            )
        })
    }

    /// Get the single constructor of the given data definition, if it is indeed
    /// a single constructor.
    pub fn get_single_ctor(&self) -> Option<CtorDefId> {
        match self.borrow().ctors {
            DataDefCtors::Defined(ctors) => match ctors.value().at(0) {
                Some(x) if ctors.value().len() == 1 => Some(x),
                _ => None,
            },
            DataDefCtors::Primitive(_) => None,
        }
    }

    /// Create a struct data definition, with some parameters.
    ///
    /// The fields are given as an iterator of `ParamData`s, which are the names
    /// and types of the fields.
    ///
    /// This will create a data definition with a single constructor, which
    /// takes the fields as parameters and returns the data type.
    pub fn struct_def(name: Symbol, params: ParamsId, fields_params: ParamsId) -> DataDefId {
        // Create the arguments for the constructor, which are the type
        // parameters given.
        let result_args = Arg::seq_from_param_names_as_vars(params);

        // Create the data definition
        Node::create_with(|id| {
            Node::at(
                DataDef {
                    name,
                    params,
                    ctors: DataDefCtors::Defined(CtorDef::seq_from_data(
                        id,
                        once({
                            CtorDefData {
                                // Name of the constructor is the same as the data definition,
                                // though we need to create a new
                                // symbol for it
                                name: name.duplicate(),
                                // The constructor is the only one
                                params: fields_params,
                                result_args,
                            }
                        }),
                    )),
                },
                NodeOrigin::Generated,
            )
        })
    }

    /// Create an enum definition, with some parameters, where each variant has
    /// specific result arguments.
    pub fn indexed_enum_def(
        name: Symbol,
        params: ParamsId,
        variants: impl Fn(DataDefId) -> Vec<(Symbol, ParamsId, Option<ArgsId>)>,
    ) -> DataDefId {
        // Create the data definition for the enum
        Node::create_with(|id| {
            Node::at(
                DataDef {
                    name,
                    params,
                    ctors: DataDefCtors::Defined(CtorDef::seq_from_data(
                        id,
                        variants(id)
                            .into_iter()
                            .map(|(variant_name, fields_params, result_args)| {
                                // Create a constructor for each variant
                                CtorDefData {
                                    name: variant_name,
                                    params: fields_params,
                                    result_args: result_args.unwrap_or_else(|| {
                                        // Create the arguments for the constructor, which are the
                                        // type parameters
                                        // given.
                                        Arg::seq_from_param_names_as_vars(params)
                                    }),
                                }
                            })
                            .collect_vec(),
                    )),
                },
                NodeOrigin::Generated,
            )
        })
    }

    /// Create an enum definition, with some parameters.
    ///
    /// The variants are given as an iterator of `(Symbol, Iter<ParamData>)`,
    /// which are the names and fields of the variants.
    ///
    /// This will create a data definition with a constructor for each variant,
    /// which takes the variant fields as parameters and returns the data
    /// type.
    pub fn enum_def(
        name: Symbol,
        params: ParamsId,
        variants: impl Fn(DataDefId) -> Vec<(Symbol, ParamsId)>,
    ) -> DataDefId {
        Self::indexed_enum_def(name, params, |def_id| {
            variants(def_id)
                .into_iter()
                .map(|(variant_name, fields_params)| (variant_name, fields_params, None))
                .collect_vec()
        })
    }
}

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
        if self.params.value().len() > 0 {
            write!(f, "({}) -> ", self.params)?;
        }

        let data_ty = DataTy { args: self.result_args, data_def: self.data_def_id };
        write!(f, "{}", &data_ty)?;

        Ok(())
    }
}

impl fmt::Display for CtorDefId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for CtorDefsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for ctor_def in self.value().iter() {
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
        if self.ctor_args.value().len() > 0 {
            write!(f, "({})", self.ctor_args)?;
        }

        Ok(())
    }
}

impl Display for CtorPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_def_id = tir_get!(self.ctor, data_def_id);
        let data_def_name = tir_get!(data_def_id, name);

        if data_def_id.borrow().ctors.assert_defined().value().len() == 1 {
            write!(f, "{data_def_name}")?;
        } else {
            let ctor_name = tir_get!(self.ctor, name);
            write!(f, "{data_def_name}::{}", ctor_name)?;
        }

        if self.ctor_pat_args.value().len() > 0 || self.ctor_pat_args_spread.is_some() {
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
            if self.params.value().len() > 0 {
                format!("<{}>", self.params)
            } else {
                "".to_string()
            },
            indent(&ctors, "  ")
        )
    }
}

impl Display for DataDefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl Display for DataTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_def_name = tir_get!(self.data_def, name);
        write!(f, "{}", data_def_name)?;
        if self.args.value().len() > 0 {
            write!(f, "<{}>", self.args)?;
        }
        Ok(())
    }
}
