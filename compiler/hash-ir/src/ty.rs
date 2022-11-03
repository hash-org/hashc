//! Simplified Hash type hierarchy. The [IrTy] is used a simplified
//! variant of the available Hash [Term]s that are defined in the
//! `hash-types` crate. This data structure is used to remove unnecessary
//! complexity from types that are required for IR generation and
//! analysis.

use std::fmt;

use bitflags::bitflags;
use hash_source::{
    constant::{FloatTy, SIntTy, UIntTy},
    identifier::Identifier,
};
use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{CloneStore, DefaultSequenceStore, DefaultStore, SequenceStore},
};
use index_vec::IndexVec;

use crate::write::{ForFormatting, WriteTyIr};

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
pub type TyStore = DefaultStore<IrTyId, IrTy>;

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
