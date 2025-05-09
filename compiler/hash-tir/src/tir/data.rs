//! Definitions related to user-defined data-types.

use core::fmt;
use std::{borrow::Borrow, fmt::Display, iter::once};

use derive_more::Deref;
use hash_storage::{
    get,
    store::{
        SequenceStoreKey, TrivialSequenceStoreKey,
        statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    },
};
use hash_target::primitives::IntTy;
use hash_utils::{bitflags::bitflags, itertools::Itertools};
use textwrap::indent;
use utility_types::Omit;

use crate::{
    stores::tir_stores,
    tir::{
        Arg, ArgsId, Node, NodeId, NodeOrigin, NodesId, ParamsId, PatArgsId, PatArgsWithSpread,
        Spread, SymbolId, TermId, TyId,
    },
    tir_node_sequence_store_direct, tir_node_single_store,
};

/// A constructor of a data-type definition.
///
/// Includes a name, the original data-type definition, an index into the
/// original data-type's constructor list, a set of parameters for the
/// constructor.
///
/// Each constructor must result in the original data-type, with some given
/// arguments.
#[derive(Debug, Copy, Clone, Omit)]
#[omit(
    arg(ident = CtorDefData, fields(data_def_id, data_def_ctor_index), derive(Debug, Clone, Copy))
)]
pub struct CtorDef {
    /// The name of the constructor, for example `symbol("Red")` in
    /// `Red: Colour` if given as a constructor to a `Colour := datatype...`.
    pub name: SymbolId,

    /// The `DataDefId` of the data-type that this constructor is a part of.
    pub data_def_id: DataDefId,

    /// An optional value/term that is used for the discriminant of the
    /// constructor.
    pub discriminant: Option<TermId>,

    /// The index of this constructor in the original data-type's ordered
    /// constructor list (`ctors`).
    pub data_def_ctor_index: usize,

    /// The parameters of the constructor.
    // @@Todo: formalise positivity requirements
    pub params: ParamsId,

    /// The arguments given to the original data-type in the "return type" of
    /// the constructor.
    ///
    /// For example, in `Red: Colour`, the `args` would be empty.
    /// In `Some: (t: T) -> Option<T>`, the `args` would be `<T>`.
    /// In `refl: (x: A) -> Id<A>(x, x)`, the `args` would be `<A>(x, x)`.
    ///
    /// This restricts the return value of each constructor to be the original
    /// data type, with some given arguments for its parameters.
    pub result_args: ArgsId,
}

tir_node_sequence_store_direct!(CtorDef);

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

bitflags! {
    /// Flags for numeric constructors.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct NumericCtorFlags: u8 {
        /// Whether the number is signed or not.
        const IS_SIGNED = 1 << 1;

        /// If the numeric is a float.
        const IS_FLOAT = 1 << 2;

        /// If the numeric is a platform dependent type.
        const IS_PLATFORM = 1 << 3;
    }
}

impl NumericCtorFlags {
    /// Check if the numeric is a float.
    pub fn is_float(self) -> bool {
        self.contains(NumericCtorFlags::IS_FLOAT)
    }

    /// Check if the numeric is signed.
    pub fn is_signed(self) -> bool {
        self.contains(NumericCtorFlags::IS_SIGNED)
    }

    /// Check if the numeric is a platform dependent type.
    pub fn is_platform(self) -> bool {
        self.contains(NumericCtorFlags::IS_PLATFORM)
    }
}

/// A numeric constructor definition.
///
/// This is a constructor which accepts numeric literals
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deref)]
pub struct NumericCtorInfo {
    /// The number of bits in the number.
    pub bits: NumericCtorBits,

    /// Flags for the numeric constructor.
    #[deref]
    pub flags: NumericCtorFlags,
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

/// Helper for creating primitive numeric constructor info.
pub(crate) fn numeric_ctors(bits: u8, flags: NumericCtorFlags) -> PrimitiveCtorInfo {
    PrimitiveCtorInfo::Numeric(NumericCtorInfo {
        bits: if bits == 0 { NumericCtorBits::Unbounded } else { NumericCtorBits::Bounded(bits) },
        flags,
    })
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

/// A utility type describing all of the needed information to create
/// an enum variant. [CtorDefData] is not used because the `args` are not
/// optional, and here they are.
#[derive(Debug, Copy, Clone, Omit)]
#[omit(
    arg(ident=VariantDataWithoutArgs, fields(result_args), derive(Debug, Clone, Copy))
)]
pub struct VariantData {
    pub name: SymbolId,
    pub params: ParamsId,
    pub result_args: Option<ArgsId>,
    pub discriminant: Option<TermId>,
}

impl CtorDef {
    /// Create data constructors from the given iterator, for the given data
    /// definition.
    pub fn seq_from_data<I: IntoIterator<Item = Node<CtorDefData>>>(
        data_def_id: DataDefId,
        data: I,
        origin: NodeOrigin,
    ) -> CtorDefsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        Node::create(Node::at(
            Node::seq(data.into_iter().enumerate().map(|(index, data)| {
                Node::at(
                    CtorDef {
                        name: data.name,
                        data_def_id,
                        discriminant: data.discriminant,
                        data_def_ctor_index: index,
                        params: data.params,
                        result_args: data.result_args,
                    },
                    data.origin,
                )
            })),
            origin,
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
#[derive(Debug, Clone, Copy, Omit)]
#[omit(
    arg(ident=DataDefData, fields(id), derive(Debug, Clone, Copy))
)]
pub struct DataDef {
    /// The name of the data-type.
    ///
    /// For example `symbol("Colour")` in `Colour := datatype...`.
    pub name: SymbolId,
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

    /// The type of the discriminant, this has no meaning to data definitions
    /// that are not enums.
    pub discriminant_ty: Option<IntTy>,
}

tir_node_single_store!(DataDef);

impl DataDef {
    /// Create an empty data definition.
    pub fn empty(
        name: SymbolId,
        params: ParamsId,
        data_origin: NodeOrigin,
        ctors_origin: NodeOrigin,
    ) -> DataDefId {
        Node::create_at(
            DataDef {
                name,
                params,
                ctors: DataDefCtors::Defined(Node::create(Node::at(
                    Node::<CtorDef>::empty_seq(),
                    ctors_origin,
                ))),
                discriminant_ty: None,
            },
            data_origin,
        )
    }

    /// Get the single constructor of the given data definition, if it is indeed
    /// a single constructor.
    pub fn get_single_ctor(&self) -> Option<CtorDefId> {
        match self.borrow().ctors {
            DataDefCtors::Defined(ctors) => match ctors.elements().at(0) {
                Some(x) if ctors.len() == 1 => Some(x),
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
    pub fn struct_def(
        name: SymbolId,
        params: ParamsId,
        fields_params: ParamsId,
        struct_origin: NodeOrigin,
    ) -> DataDefId {
        // Create the arguments for the constructor, which are the type
        // parameters given.
        let result_args = Arg::seq_from_param_names_as_vars(params);

        // Create the data definition
        Node::create_with(|id| {
            Node::at(
                DataDef {
                    name,
                    params,
                    discriminant_ty: None,
                    ctors: DataDefCtors::Defined(CtorDef::seq_from_data(
                        id,
                        once({
                            Node::at(
                                CtorDefData {
                                    // Struct does't have a value for the discriminant.
                                    discriminant: None,
                                    // Name of the constructor is the same as the data definition,
                                    // though we need to create a new
                                    // symbol for it
                                    name: name.duplicate(name.origin()),
                                    // The constructor is the only one
                                    params: fields_params,
                                    result_args,
                                },
                                fields_params.origin(),
                            )
                        }),
                        fields_params.origin(),
                    )),
                },
                struct_origin,
            )
        })
    }

    /// Create an enum definition, with some parameters, where each variant has
    /// specific result arguments.
    pub fn indexed_enum_def(
        name: SymbolId,
        discriminant_ty: IntTy,
        params: ParamsId,
        variants: impl FnOnce(DataDefId) -> Node<Vec<Node<VariantData>>>,
        enum_origin: NodeOrigin,
    ) -> DataDefId {
        // Create the data definition for the enum
        Node::create_with(|id| {
            let variants = variants(id);
            let variants_origin = variants.origin;

            // Create a constructor for each variant
            let ctor_defs = CtorDef::seq_from_data(
                id,
                variants
                    .data
                    .into_iter()
                    .map(|node| {
                        let VariantData { name, params: field_params, result_args, discriminant } =
                            *node;
                        Node::at(
                            CtorDefData {
                                name,
                                params: field_params,
                                discriminant,
                                result_args: result_args.unwrap_or_else(|| {
                                    // Create the arguments for the constructor, which
                                    // are the type parameters given.
                                    Arg::seq_from_param_names_as_vars(params)
                                }),
                            },
                            node.origin,
                        )
                    })
                    .collect_vec(),
                variants_origin,
            );

            Node::at(
                DataDef {
                    name,
                    params,
                    ctors: DataDefCtors::Defined(ctor_defs),
                    discriminant_ty: Some(discriminant_ty),
                },
                enum_origin,
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
        name: SymbolId,
        discriminant_ty: IntTy,
        params: ParamsId,
        variants: impl FnOnce(DataDefId) -> Node<Vec<Node<VariantDataWithoutArgs>>>,
        enum_origin: NodeOrigin,
    ) -> DataDefId {
        Self::indexed_enum_def(
            name,
            discriminant_ty,
            params,
            |def_id| {
                let variants = variants(def_id);
                Node::at(
                    variants
                        .data
                        .into_iter()
                        .map(|node| {
                            node.with_data(VariantData {
                                name: node.name,
                                params: node.params,
                                result_args: None,
                                discriminant: node.discriminant,
                            })
                        })
                        .collect_vec(),
                    variants.origin,
                )
            },
            enum_origin,
        )
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
        write!(f, "{}", *self.value())
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
        let (ctor_name, data_def_id) = (get!(self.ctor, name), get!(self.ctor, data_def_id));

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
        let data_def_id = get!(self.ctor, data_def_id);
        let data_def_name = get!(data_def_id, name);

        if data_def_id.borrow().ctors.assert_defined().len() == 1 {
            write!(f, "{data_def_name}")?;
        } else {
            let ctor_name = get!(self.ctor, name);
            write!(f, "{data_def_name}::{}", ctor_name)?;
        }

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
                    "numeric [bits={}, float={}, signed={}, platform={}]",
                    numeric.bits,
                    numeric.flags.contains(NumericCtorFlags::IS_FLOAT),
                    numeric.flags.contains(NumericCtorFlags::IS_SIGNED),
                    numeric.flags.contains(NumericCtorFlags::IS_PLATFORM)
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
        write!(f, "{}", *self.value())
    }
}

impl Display for DataTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_def_name = get!(self.data_def, name);
        write!(f, "{}", data_def_name)?;
        if self.args.len() > 0 {
            write!(f, "<{}>", self.args)?;
        }
        Ok(())
    }
}
