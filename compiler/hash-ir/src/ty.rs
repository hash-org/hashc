//! Simplified Hash type hierarchy. The [IrTy] is used a simplified
//! variant of the available Hash [Term]s that are defined in the
//! `hash-types` crate. This data structure is used to remove unnecessary
//! complexity from types that are required for IR generation and
//! analysis.

use std::{cell::Cell, fmt};

use bitflags::bitflags;
use hash_source::{
    constant::{FloatTy, IntTy, SIntTy, UIntTy},
    identifier::Identifier,
};
use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{CloneStore, DefaultSequenceStore, DefaultStore, SequenceStore, Store},
};
use index_vec::{index_vec, IndexVec};

use crate::{
    write::{ForFormatting, WriteTyIr},
    IrStorage,
};

/// Mutability of a particular variable, reference, etc.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mutability {
    /// Mutable variable, reference, etc.
    Mutable,
    /// Immutable variable, reference, etc.
    Immutable,
}

impl Mutability {
    /// Returns true if the mutability is mutable.
    pub fn is_mutable(&self) -> bool {
        matches!(self, Mutability::Mutable)
    }

    /// Returns true if the mutability is immutable.
    pub fn is_immutable(&self) -> bool {
        matches!(self, Mutability::Immutable)
    }

    /// Get [Mutability] as a printable name
    pub fn as_str(&self) -> &'static str {
        match self {
            Mutability::Mutable => "mut ",
            Mutability::Immutable => "",
        }
    }
}

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Simplified type structure used by the IR and other stages to reason about
/// Hash programs once types have been erased and simplified.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IrTy {
    /// A primitive signed integer type, e.g. `i32`.
    Int(SIntTy),

    /// A primitive unsigned integer type, e.g. `u32`.
    UInt(UIntTy),

    /// A primitive floating point type, e.g. `f32`.
    Float(FloatTy),

    /// String type.
    Str,

    /// Boolean type.
    Bool,

    /// Character type.
    Char,

    /// The never type
    Never,

    /// A reference type, referring to a another type, e.g. `&T`
    Ref(IrTyId, Mutability),

    /// A raw reference type, referring to a another type, e.g. `&raw T`
    RawRef(IrTyId, Mutability),

    /// A reference counted pointer type, e.g. `Rc<T>`
    Rc(IrTyId, Mutability),

    /// A slice type
    Slice(IrTyId),

    /// An array type with a specified length, i.e. `[T; N]`
    Array(IrTyId, u64),

    /// An abstract data structure type, i.e a `struct` or `enum`, or any
    /// other kind of type.
    Adt(AdtId),

    /// The first item is the interned parameter types to the function, and the
    /// second item is the return type of the function. If the function has no
    /// explicit return type, this will always be inferred at this stage.
    Fn(IrTyListId, IrTyId),
}

impl IrTy {
    /// Make a unit type, i.e. `()`
    pub fn unit(ir_storage: &IrStorage) -> Self {
        let variants = index_vec![AdtVariant { name: 0usize.into(), fields: vec![] }];
        let adt = AdtData::new_with_flags("unit".into(), variants, AdtFlags::TUPLE);
        let adt_id = ir_storage.adt_store().create(adt);

        Self::Adt(adt_id)
    }

    /// Make a tuple type, i.e. `(T1, T2, T3, ...)`
    pub fn tuple(ir_storage: &IrStorage, tys: &[IrTyId]) -> Self {
        let variants = index_vec![AdtVariant {
            name: 0usize.into(),
            fields: tys
                .iter()
                .copied()
                .enumerate()
                .map(|(idx, ty)| AdtField { name: idx.into(), ty })
                .collect(),
        }];
        let adt = AdtData::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
        let adt_id = ir_storage.adt_store().create(adt);

        Self::Adt(adt_id)
    }

    /// Check if the type is an integral type.
    pub fn is_integral(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_) | Self::Float(_) | Self::Char)
    }
}

impl From<IntTy> for IrTy {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::Int(ty) => Self::Int(ty),
            IntTy::UInt(ty) => Self::UInt(ty),
        }
    }
}

index_vec::define_index_type! {
    /// Index for [VariantIdx] stores within generated [Body]s.
    pub struct VariantIdx = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "variant#{}";
}

#[derive(Clone)]
pub struct AdtData {
    /// The name of the ADT
    pub name: Identifier,

    /// All of the variants that are defined for this variant.
    pub variants: IndexVec<VariantIdx, AdtVariant>,

    // Flags which denote additional information about this specific
    // data structure.
    pub flags: AdtFlags,

    /// Options that are regarding the representation of the ADT
    /// in memory.
    pub representation: AdtRepresentation,
}

impl AdtData {
    /// Create a new [AdtData] with the given name and variants.
    pub fn new(name: Identifier, variants: IndexVec<VariantIdx, AdtVariant>) -> Self {
        Self {
            name,
            variants,
            representation: AdtRepresentation::default(),
            flags: AdtFlags::empty(),
        }
    }

    /// Create [AdtData] with specified [AdtFlags].
    pub fn new_with_flags(
        name: Identifier,
        variants: IndexVec<VariantIdx, AdtVariant>,
        flags: AdtFlags,
    ) -> Self {
        Self { name, variants, representation: AdtRepresentation::default(), flags }
    }
}

bitflags! {
    /// Flags that occur on a [AdtData] which are used for conveniently checking
    /// the properties of the underlying ADT.
    pub struct AdtFlags: u32 {
        /// The underlying ADT is a union.
        const UNION = 0b00000001;

        /// The underlying ADT is a struct.
        const STRUCT  = 0b00000010;

        /// The underlying ADT is a enum.
        const ENUM  = 0b00000100;

        /// The underlying ADT is a tuple.
        const TUPLE  = 0b00001000;
    }
}

/// Options that are regarding the representation of the ADT. This includes
/// options about alignment, padding, etc.
///
/// @@Future: add user configurable options for the ADT.
///     - add `alignment` configuration
///     - add `pack` configuration
///     - add layout randomisation configuration
///     - add `C` layout configuration
#[derive(Clone)]
pub struct AdtRepresentation {}
impl AdtRepresentation {
    fn default() -> AdtRepresentation {
        AdtRepresentation {}
    }
}

#[derive(Clone)]
pub struct AdtVariant {
    /// The name of the variant, if this is a struct variant, this inherits
    /// the name of the struct.
    pub name: Identifier,

    /// The fields that are defined for this variant.
    pub fields: Vec<AdtField>,
}

#[derive(Clone)]
pub struct AdtField {
    /// The name of the field.
    pub name: Identifier,

    /// The type of the field.
    pub ty: IrTyId,
}

new_store_key!(pub AdtId);

/// Stores all the used [IrTy]s.
///
/// [Rvalue]s are accessed by an ID, of type [IrTyId].
pub type AdtStore = DefaultStore<AdtId, AdtData>;

impl fmt::Display for ForFormatting<'_, AdtId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let adt = self.storage.adt_store().get(self.t);

        match adt.flags {
            AdtFlags::TUPLE => {
                assert!(adt.variants.len() == 1);
                let variant = &adt.variants[0];

                write!(f, "(")?;
                for (i, field) in variant.fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", field.ty.for_fmt(self.storage))?;
                }

                write!(f, ")")
            }
            _ => {
                // We just write the name of the underlying ADT
                write!(f, "{}", adt.name)
            }
        }
    }
}

new_store_key!(pub IrTyId);

/// Stores all the used [IrTy]s.
///
/// [Rvalue]s are accessed by an ID, of type [IrTyId].
#[derive(Debug, Default)]
pub struct TyStore {
    data: DefaultStore<IrTyId, IrTy>,

    /// Internal boolean used sometimes when lowering binary expressions
    /// that need to be checked.
    bool_ty: Cell<Option<IrTyId>>,
}

impl TyStore {
    /// Create a [IrTy::Bool], this will re-use the previously created boolean
    /// type if it exists.
    pub fn make_bool(&self) -> IrTyId {
        if let Some(id) = self.bool_ty.get() {
            id
        } else {
            let id = self.create(IrTy::Bool);
            self.bool_ty.set(Some(id));
            id
        }
    }
}

impl Store<IrTyId, IrTy> for TyStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<IrTy>> {
        self.data.internal_data()
    }
}

impl fmt::Display for ForFormatting<'_, IrTyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ty = self.storage.ty_store().get(self.t);

        match ty {
            IrTy::Int(variant) => write!(f, "{variant}"),
            IrTy::UInt(variant) => write!(f, "{variant}"),
            IrTy::Float(variant) => write!(f, "{variant}"),
            IrTy::Bool => write!(f, "bool"),
            IrTy::Str => write!(f, "str"),
            IrTy::Char => write!(f, "char"),
            IrTy::Never => write!(f, "!"),
            IrTy::Ref(inner, mutability) => {
                write!(f, "&{mutability}{}", inner.for_fmt(self.storage))
            }
            IrTy::RawRef(inner, mutability) => {
                write!(f, "&raw {mutability}{}", inner.for_fmt(self.storage))
            }
            IrTy::Rc(inner, mutability) => {
                let name = match mutability {
                    Mutability::Mutable => "Mut",
                    Mutability::Immutable => "",
                };

                write!(f, "Rc{name}<{}>", inner.for_fmt(self.storage))
            }
            IrTy::Adt(adt) => write!(f, "{}", adt.for_fmt(self.storage)),
            IrTy::Fn(params, return_ty) => write!(
                f,
                "({}) -> {}",
                params.for_fmt(self.storage),
                return_ty.for_fmt(self.storage)
            ),
            IrTy::Slice(ty) => write!(f, "[{}]", ty.for_fmt(self.storage)),
            IrTy::Array(ty, len) => write!(f, "[{}; {len}]", ty.for_fmt(self.storage)),
        }
    }
}

new_sequence_store_key!(pub IrTyListId);

/// Define the [TyListStore], which is a sequence of [IrTy]s associated
/// with a [IrTyListId].
pub type TyListStore = DefaultSequenceStore<IrTyListId, IrTyId>;

impl fmt::Display for ForFormatting<'_, IrTyListId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let items = self.storage.ty_list_store().get_vec(self.t);
        let mut tys = items.iter();

        if let Some(first) = tys.next() {
            write!(f, "{first}", first = first.for_fmt(self.storage))?;

            for ty in tys {
                write!(f, ", {ty}", ty = ty.for_fmt(self.storage))?;
            }
        }

        Ok(())
    }
}
