//! Simplified Hash type hierarchy. The [IrTy] is used a simplified
//! variant of the available Hash [Term]s that are defined in the
//! `hash-tir` crate. This data structure is used to remove unnecessary
//! complexity from types that are required for IR generation and
//! analysis.

use std::{cmp, fmt};

use bitflags::bitflags;
use hash_ast::ast;
use hash_source::{
    attributes::ItemAttributes,
    constant::{FloatTy, IntTy, SIntTy, UIntTy},
    identifier::Identifier,
    SourceId,
};
use hash_target::{
    abi::{self, Integer, ScalarKind},
    data_layout::HasDataLayout,
    size::Size,
};
use hash_utils::{
    index_vec::{self, index_vec, IndexVec},
    new_sequence_store_key, new_store_key,
    store::{CloneStore, DefaultSequenceStore, DefaultStore, SequenceStore, Store, StoreKey},
};

use crate::{
    ir::{LocalDecls, Place, PlaceProjection},
    write::{ForFormatting, WriteIr},
    IrCtx,
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

impl From<ast::Mutability> for Mutability {
    fn from(value: ast::Mutability) -> Self {
        match value {
            ast::Mutability::Mutable => Mutability::Mutable,
            ast::Mutability::Immutable => Mutability::Immutable,
        }
    }
}

impl From<hash_tir::old::scope::Mutability> for Mutability {
    fn from(value: hash_tir::old::scope::Mutability) -> Self {
        use hash_tir::old::scope::Mutability::*;

        match value {
            Mutable => Mutability::Mutable,
            Immutable => Mutability::Immutable,
        }
    }
}

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

new_store_key!(pub InstanceId);

/// This is a temporary struct that identifies a unique instance of a
/// function within the generated code, and is later used to resolve
/// function references later on.
#[derive(Debug, Clone)]
pub struct Instance {
    /// The fully specified name of the function instance.
    ///
    /// @@Future: this should really be a path in the the module
    /// that it was defined.
    name: Identifier,

    /// A reference to the parameter types of this function
    /// instance.
    pub params: IrTyListId,

    /// The function return type.
    pub ret_ty: IrTyId,

    /// Any attributes that are present  on the instance, this is used
    /// to specify special behaviour of the function.
    pub attributes: ItemAttributes,

    /// The source of this function instance. This is useful
    /// for when symbol names are mangled, and we need to
    /// include a reference to where it was defined.
    ///
    /// @@Future: Ideally, this information should deduce a namespaced
    /// path to the module location instead of just using the module
    /// id as the disambiguator.
    pub source: Option<SourceId>,

    /// If the instance refers to an intrinsic function, and will be converted
    /// into possibly some different code.
    pub is_intrinsic: bool,

    /// If the function instance originates from a generic function.
    generic_origin: bool,
}

impl Instance {
    /// Create a new instance.
    pub fn new(
        name: Identifier,
        source: Option<SourceId>,
        params: IrTyListId,
        ret_ty: IrTyId,
    ) -> Self {
        Self {
            name,
            is_intrinsic: false,
            params,
            source,
            ret_ty,
            generic_origin: false,
            attributes: ItemAttributes::default(),
        }
    }

    /// Get the name from the instance.
    pub fn name(&self) -> Identifier {
        self.name
    }

    /// Check if the instance is of a generic origin.
    pub fn is_generic_origin(&self) -> bool {
        self.generic_origin
    }

    /// Check if the [Instance] is an intrinsic function.
    pub fn is_intrinsic(&self) -> bool {
        self.is_intrinsic
    }
}

/// Stores all the used [Instance]s.
///
/// [Instance]s are accessed by an ID, of type [InstanceId].
pub struct InstanceStore {
    /// The underlying store.
    store: DefaultStore<InstanceId, Instance>,
}

impl InstanceStore {
    /// Create a new [InstanceStore].
    pub fn new() -> Self {
        Self { store: DefaultStore::new() }
    }

    /// Get the name of an instance from its [InstanceId].
    pub fn name_of(&self, instance: InstanceId) -> Identifier {
        self.store.map_fast(instance, |instance| instance.name)
    }
}

impl Default for InstanceStore {
    fn default() -> Self {
        Self::new()
    }
}

impl Store<InstanceId, Instance> for InstanceStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<Instance>> {
        self.store.internal_data()
    }
}

/// Reference kind, e.g. `&T`, `&mut T`, `&raw T` or `Rc<T>`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RefKind {
    /// Normal reference kind, e.g. `&T` or `&mut T`
    Normal,

    /// Raw reference kind e.g. `&raw T`
    Raw,

    /// Reference counted reference kind.
    Rc,
}

impl fmt::Display for RefKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefKind::Normal => write!(f, ""),
            RefKind::Raw => write!(f, "raw "),
            RefKind::Rc => write!(f, "rc "),
        }
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

    /// A reference type, referring to a another type, e.g. `&T`, `&mut T`
    /// or `&raw T`, or `Rc<T>`.
    Ref(IrTyId, Mutability, RefKind),

    /// A slice type
    Slice(IrTyId),

    /// An array type with a specified length, i.e. `[T; N]`
    Array { ty: IrTyId, length: usize },

    /// An abstract data structure type, i.e a `struct` or `enum`, or any
    /// other kind of type.
    Adt(AdtId),

    /// A function type, with interned parameter type list and a return
    /// type.
    Fn {
        /// The parameter types of the function.
        params: IrTyListId,

        /// The return type of the function.
        return_ty: IrTyId,
    },

    /// A function definition, it has an associated instance which denotes
    /// information about the function, such as the name, defining module,
    /// ABI, etc.
    FnDef {
        /// An [Instance] refers to the function that this type refers to. The
        /// instance records information about the function instance,
        /// like the name, the specified function attributes (i.e.
        /// linkage), etc.
        instance: InstanceId,
    },
}

impl IrTy {
    /// Make a tuple type, i.e. `(T1, T2, T3, ...)`
    pub fn tuple(ctx: &IrCtx, tys: &[IrTyId]) -> Self {
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
        let adt_id = ctx.adts().create(adt);

        Self::Adt(adt_id)
    }

    /// Create a reference type to the provided [IrTy].
    pub fn make_ref(ty: IrTy, ctx: &IrCtx) -> Self {
        Self::Ref(ctx.tys().create(ty), Mutability::Immutable, RefKind::Normal)
    }

    /// Check if a type is a reference type.
    pub fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_, _, _))
    }

    /// Check if the [IrTy] is an integral type.
    pub fn is_integral(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_))
    }

    /// Check whether the [IrTy] is "switchable", as in if
    /// it can be compared without any additional work. This
    /// is primarily used for generating code for `match` statements.
    pub fn is_switchable(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_) | Self::Char | Self::Bool)
    }

    /// Check if the [IrTy] is a floating point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float(_))
    }

    /// Check if the [IrTy] is a signed integral type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Check if a [IrTy] is a function type.
    pub fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    /// Check if a type is a scalar, i.e. it cannot be divided into
    /// further components. [`IrTy::Ref(..)`] with non-[`RefKind::Rc`] is also
    /// considered as a scalar since the components of the reference are
    /// *opaque* to the compiler because it isn't managed.
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            Self::Int(_)
                | Self::UInt(_)
                | Self::Float(_)
                | Self::Char
                | Self::Bool
                | Self::Ref(_, _, RefKind::Normal | RefKind::Raw)
        )
    }

    /// Check if the type is an array.
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array { .. })
    }

    /// Check if the type is an ADT.
    pub fn is_adt(&self) -> bool {
        matches!(self, Self::Adt(_))
    }

    /// Assuming that the [IrTy] is an ADT, return the [AdtId]
    /// of the underlying ADT.
    pub fn as_adt(&self) -> AdtId {
        match self {
            Self::Adt(adt_id) => *adt_id,
            ty => panic!("expected ADT, but got {ty:?}"),
        }
    }

    /// Assuming that the [IrTy] is an ADT, return the [AdtId]
    /// of the underlying ADT.
    pub fn as_instance(&self) -> InstanceId {
        match self {
            Self::FnDef { instance } => *instance,
            ty => panic!("expected fn def, but got {ty:?}"),
        }
    }

    /// Get the type of this [IrTy] if a dereference is performed on it.
    pub fn on_deref(&self) -> Option<IrTyId> {
        match self {
            Self::Ref(ty, _, _) => Some(*ty),
            _ => None,
        }
    }

    /// Get the type of this [IrTy] if an index operation
    /// is performed on it.
    pub fn on_index(&self) -> Option<IrTyId> {
        match self {
            Self::Slice(ty) | Self::Array { ty, .. } => Some(*ty),
            _ => None,
        }
    }

    /// Get the type of this [IrTy] if a field access is performed on it.
    /// Optionally, the function can be supplied a [VariantIdx] in order to
    /// access a particular variant of the ADT (for `enum`s and `union`s).
    pub fn on_field_access(
        &self,
        field: usize,
        variant: Option<VariantIdx>,
        ctx: &IrCtx,
    ) -> Option<IrTyId> {
        match self {
            IrTy::Adt(id) => ctx.map_adt(*id, |_, adt| {
                let variant = match variant {
                    Some(variant) => adt.variant(variant),
                    None => adt.univariant(),
                };

                Some(variant.field(field).ty)
            }),
            _ => None,
        }
    }

    /// Compute the discriminant value for a particular [IrTy] and
    /// evaluate it to a raw value.
    pub fn discriminant_for_variant(
        &self,
        ctx: &IrCtx,
        variant: VariantIdx,
    ) -> Option<(IntTy, u128)> {
        match self {
            IrTy::Adt(id) => {
                ctx.adts().map_fast(*id, |data| {
                    if !data.flags.is_enum() || data.variants.is_empty() {
                        None
                    } else {
                        // We get the offset of the current discriminant and then
                        // we also compute the "initial" value of the discriminant
                        // for this type. Currently, this is quite trivial to do
                        // since the user cannot (yet) modify what the discriminant
                        // of each enum variant is, and thus we don't need to account
                        // for this.
                        let discriminant_value = data.discriminant_value_for(variant);
                        let discriminant_type = data.discriminant_ty();

                        Some((discriminant_type, discriminant_value as u128))
                    }
                })
            }
            _ => None,
        }
    }

    /// Compute the discriminant type for the given type. This computes
    /// the specific "discriminant" for `enum` ADTs, and simply returns a
    /// `u8` for all other types. This is because the discriminant type of
    /// all other types is considered to be `0`, and thus a `u8` is sufficient.
    pub fn discriminant_ty(&self, ctx: &IrCtx) -> IrTyId {
        match self {
            IrTy::Adt(id) => ctx.map_adt(*id, |_, data| {
                if data.flags.is_enum() {
                    data.discriminant_ty().to_ir_ty(ctx)
                } else {
                    ctx.tys().common_tys.u8
                }
            }),
            IrTy::Int(_)
            | IrTy::UInt(_)
            | IrTy::Float(_)
            | IrTy::Str
            | IrTy::Bool
            | IrTy::Char
            | IrTy::Never
            | IrTy::Ref(_, _, _)
            | IrTy::Slice(_)
            | IrTy::Array { .. }
            | IrTy::FnDef { .. }
            | IrTy::Fn { .. } => ctx.tys().common_tys.u8,
        }
    }

    /// Attempt to compute the type of an element from an [`IrTy::Slice`] or
    /// [`IrTy::Array`]. If the type is not a slice or array, then `None` is
    /// returned.
    pub fn element_ty(&self, ctx: &IrCtx) -> Option<IrTyId> {
        match self {
            IrTy::Slice(ty) | IrTy::Array { ty, .. } => Some(*ty),
            IrTy::Ref(ty, _, _) => ctx.tys().map_fast(*ty, |ty| ty.element_ty(ctx)),
            _ => None,
        }
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

impl From<IrTy> for IntTy {
    fn from(ty: IrTy) -> Self {
        match ty {
            IrTy::Int(ty) => Self::Int(ty),
            IrTy::UInt(ty) => Self::UInt(ty),
            _ => panic!("expected integral type, but got {ty:?}"),
        }
    }
}

index_vec::define_index_type! {
    /// Index for [VariantIdx] stores within generated [Body]s.
    pub struct VariantIdx = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "variant#{}";

    DISPLAY_FORMAT="{}";
}

/// This is the underlying data of an ADT which is stored behind an [AdtId].
/// The ADT stores the name of the defined type, all of the variants (if it
/// a leaf ADT i.e. `struct` or `tuple` then there is one variant), and
/// information about the ADT, which kind of ADT it is, and how it is
/// represented in memory.
#[derive(Clone, Debug)]
pub struct AdtData {
    /// The name of the ADT
    pub name: Identifier,

    /// All of the variants that are defined for this variant.
    pub variants: IndexVec<VariantIdx, AdtVariant>,

    /// Any type substitutions that appeared when the type was
    /// lowered. This is not important for the type itself, but for
    /// printing the type, and computing the name of the type does
    /// depend on this information.
    pub substitutions: Option<IrTyListId>,

    // Flags which denote additional information about this specific
    // data structure.
    pub flags: AdtFlags,

    /// Options that are regarding the representation of the ADT
    /// in memory.
    pub metadata: AdtRepresentation,
}

impl AdtData {
    /// Create a new [AdtData] with the given name and variants.
    pub fn new(name: Identifier, variants: IndexVec<VariantIdx, AdtVariant>) -> Self {
        Self {
            name,
            variants,
            metadata: AdtRepresentation::default(),
            flags: AdtFlags::empty(),
            substitutions: None,
        }
    }

    /// Create [AdtData] with specified [AdtFlags].
    pub fn new_with_flags(
        name: Identifier,
        variants: IndexVec<VariantIdx, AdtVariant>,
        flags: AdtFlags,
    ) -> Self {
        Self { name, variants, metadata: AdtRepresentation::default(), flags, substitutions: None }
    }

    /// Get the variant at the given [VariantIdx].
    pub fn variant(&self, idx: VariantIdx) -> &AdtVariant {
        &self.variants[idx]
    }

    /// Get the univariant of the ADT. This is only valid for ADTs that
    /// have a single variant, i.e. `struct`s and `tuple`s.`
    pub fn univariant(&self) -> &AdtVariant {
        assert!(self.flags.is_struct() || self.flags.is_tuple());
        &self.variants[VariantIdx::new(0)]
    }

    /// Lookup the index of a variant by its name.
    pub fn variant_idx(&self, name: &Identifier) -> Option<VariantIdx> {
        self.variants.position(|variant| &variant.name == name)
    }

    /// Compute the discriminant type of this ADT, assuming that this
    /// is an `enum` or a `union`.
    ///
    /// @@Future(discriminants): This is incomplete because it does not account
    /// for the `repr` attribute, and the fact that enums might have
    /// explicit discriminants specified on them.
    pub fn discriminant_ty(&self) -> IntTy {
        debug_assert!(self.flags.is_enum() || self.flags.is_union());

        // Compute the maximum number of bits needed for the discriminant.
        let max = self.variants.len() as u64;
        let bits = max.leading_zeros();
        let size = Size::from_bits(cmp::max(1, 64 - bits));

        IntTy::UInt(UIntTy::from_size(size))
    }

    /// Compute the representation of the discriminant of this [AdtData]
    /// in terms of a [abi::Integer].
    ///
    /// @@Future(discriminants): we would need to account for different
    /// representations of the discriminant, e.g. `repr(u8)`, and specified
    /// values on the discriminant.
    ///
    /// For now, we always use the "unsigned" integer representation, and try
    /// to minimise the size of the discriminant.
    pub fn discriminant_representation<C: HasDataLayout>(&self, ctx: &C) -> abi::Integer {
        let max = self.variants.len() as u128;
        let computed_fit = abi::Integer::fit_unsigned(max);

        // If this is a C-like representation, then we always
        // default to the tag enum size specified by the target.
        let minimum = if self.metadata.is_c_like() {
            ctx.data_layout().c_style_enum_min_size
        } else {
            Integer::I8
        };

        cmp::max(computed_fit, minimum)
    }

    /// Compute the discriminant value for a particular variant.
    pub fn discriminant_value_for(&self, variant: VariantIdx) -> u32 {
        debug_assert!(self.flags.is_enum());

        // @@Future(discriminants): We don't account for user specified
        // discriminants just yet, so this is simply the index of the
        // variant.
        variant._raw
    }

    /// Create an iterator of all of the discriminants of this ADT.
    pub fn discriminants(&self) -> impl Iterator<Item = (VariantIdx, u128)> {
        self.variants.indices().map(|idx| (idx, idx._raw as u128))
    }
}

bitflags! {
    /// Flags that occur on a [AdtData] which are used for conveniently checking
    /// the properties of the underlying ADT.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl AdtFlags {
    /// Check if the underlying ADT is a union.
    pub fn is_union(&self) -> bool {
        self.contains(Self::UNION)
    }

    /// Check if the underlying ADT is a struct.
    pub fn is_struct(&self) -> bool {
        self.contains(Self::STRUCT)
    }

    /// Check if the underlying ADT is a enum.
    pub fn is_enum(&self) -> bool {
        self.contains(Self::ENUM)
    }

    /// Check if the underlying ADT is a tuple.
    pub fn is_tuple(&self) -> bool {
        self.contains(Self::TUPLE)
    }
}

bitflags! {
    /// Flags that represent information about the representation of the ADT.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct RepresentationFlags: u32 {
        /// The ADT is a C-like type, and hence adheres to the C ABI and C
        /// layout rules.
        const C_LIKE = 0b00000001;
    }
}

/// Options that are regarding the representation of the ADT. This includes
/// options about alignment, padding, etc.
///
/// @@Future: add user configurable options for the ADT.
///     - add `alignment` configuration
///     - add `pack` configuration
///     - add layout randomisation configuration
#[derive(Clone, Debug, Default)]
pub struct AdtRepresentation {
    /// Flags that determine the representation of the type. Currently, if
    /// no flags are set the type is treated normally, if the `C_LIKE` flag
    /// is set, then the type is treated as a C-like type, and hence adheres
    /// to the C ABI and C layout rules
    representation: RepresentationFlags,
}

impl AdtRepresentation {
    /// Specify [RepresentationFlags] on the [AdtRepresentation].
    pub fn add_flags(&mut self, flags: RepresentationFlags) {
        self.representation |= flags;
    }

    /// Check if the representation of the ADT is specified to
    /// be in C-style layout.
    pub fn is_c_like(&self) -> bool {
        self.representation.contains(RepresentationFlags::C_LIKE)
    }

    /// Check whether the [AdtRepresentation] permits the re-ordering
    /// of struct fields in order to optimise for memory layout.
    pub fn inhibits_struct_field_reordering(&self) -> bool {
        self.is_c_like()
    }

    /// Check whether the [AdtRepresentation] (an underlying `union`) permits
    /// it's ABI to be optimised into a scalar-like form.
    pub fn inhibits_union_abi_optimisations(&self) -> bool {
        self.is_c_like()
    }
}

/// An [AdtVariant] is a potential variant of an ADT which contains all of the
/// associated fields, and the name of the variant if any. If no names are
/// available, then the name will be the index of that variant.
#[derive(Clone, Debug)]
pub struct AdtVariant {
    /// The name of the variant, if this is a struct variant, this inherits
    /// the name of the struct.
    pub name: Identifier,

    /// The fields that are defined for this variant.
    pub fields: Vec<AdtField>,
}

impl AdtVariant {
    /// Find the index of a field by name.
    pub fn field_idx(&self, name: Identifier) -> Option<usize> {
        self.fields.iter().position(|field| field.name == name)
    }

    /// Get the field at the given index.
    pub fn field(&self, idx: usize) -> &AdtField {
        &self.fields[idx]
    }
}

/// A alias for the variants of an ADT.
pub type AdtVariants = IndexVec<VariantIdx, AdtVariant>;

/// An [AdtField] is a field that is defined for a variant of an ADT. It
/// contains an associated name, and a type. If no user defined name was
/// available, then the name of each variant is the index of that field.
#[derive(Clone, Debug)]
pub struct AdtField {
    /// The name of the field.
    pub name: Identifier,

    /// The type of the field.
    pub ty: IrTyId,
}

new_store_key!(pub AdtId);

impl AdtId {
    /// The unit type always uses the first ID in the store.
    pub const UNIT: AdtId = AdtId { index: 0 };
}

/// Stores all the used [AdtData]s. An [AdtData] is all of the
/// information about an ADT, including variants, fields, representation,
/// and any other additional attributes.
///
/// [AdtData]s are accessed by an ID, of type [AdtId].
pub struct AdtStore {
    /// The underlying store.
    store: DefaultStore<AdtId, AdtData>,
}

impl AdtStore {
    /// Create a new [AdtStore], and initialise the store
    /// with the unit type.
    pub fn new() -> AdtStore {
        let store = DefaultStore::new();

        let variants = index_vec![AdtVariant { name: 0usize.into(), fields: vec![] }];
        let adt = AdtData::new_with_flags("unit".into(), variants, AdtFlags::TUPLE);

        let id = store.create(adt);
        assert!(AdtId::UNIT == id);

        Self { store }
    }
}

impl Default for AdtStore {
    fn default() -> Self {
        Self::new()
    }
}

impl Store<AdtId, AdtData> for AdtStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<AdtData>> {
        self.store.internal_data()
    }
}

impl fmt::Display for ForFormatting<'_, AdtId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.adts().map_fast(self.item, |adt| {
            match adt.flags {
                AdtFlags::TUPLE => {
                    assert!(adt.variants.len() == 1);
                    let variant = &adt.variants[0];

                    write!(f, "(")?;
                    for (i, field) in variant.fields.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }

                        write!(f, "{}", field.ty.for_fmt(self.ctx))?;
                    }

                    write!(f, ")")
                }
                _ => {
                    // We just write the name of the underlying ADT
                    write!(f, "{}", adt.name)?;

                    // If there are type arguments, then we write them
                    // out as well.
                    if let Some(args) = adt.substitutions {
                        write!(f, "<")?;
                        self.ctx.tls().map_fast(args, |args| {
                            for (i, arg) in args.iter().enumerate() {
                                if i != 0 {
                                    write!(f, ", ")?;
                                }

                                write!(f, "{}", arg.for_fmt(self.ctx))?;
                            }

                            Ok(())
                        })?;

                        write!(f, ">")?;
                    }

                    Ok(())
                }
            }
        })
    }
}

new_store_key!(pub IrTyId);

/// Macro that is used to create the "common" IR types. Each
/// entry has an associated name, and then followed by the type
/// expression that represents the [IrTy].
macro_rules! create_common_ty_table {
    ($($name:ident: $value:expr),* $(,)?) => {

        /// Defines a map of common types that might be used in the IR
        /// and general IR operations. When creating new types that refer
        /// to these common types, they should be created using the
        /// using the associated [IrTyId]s of this map.
        pub struct CommonIrTys {
            $(pub $name: IrTyId, )*

            /// A slice of bytes, i.e. `[u8]`.
            pub byte_slice: IrTyId,

            /// A string, i.e. `&str`.
            pub str: IrTyId,

            /// A general pointer to bytes, i.e. `&u8`.
            pub ptr: IrTyId,

            /// A general pointer to bytes, i.e. `&raw u8`.
            pub raw_ptr: IrTyId,

            /// A void pointer, i.e. `&()`.
            pub void_ptr: IrTyId,
        }

        impl CommonIrTys {
            pub fn new(data: &DefaultStore<IrTyId, IrTy>) -> CommonIrTys {
                let table = CommonIrTys {
                    $($name: data.create($value), )*
                    byte_slice: IrTyId::from_index_unchecked(0),
                    ptr: IrTyId::from_index_unchecked(0),
                    raw_ptr: IrTyId::from_index_unchecked(0),
                    void_ptr: IrTyId::from_index_unchecked(0),
                    str: IrTyId::from_index_unchecked(0),
                };

                // @@Hack: find a way to nicely create this within the `create_common_ty_table!`,
                // however this would require somehow referencing entries within the table before
                // they are defined...
                let byte_slice = data.create(IrTy::Slice(table.u8));
                let ptr = data.create(IrTy::Ref(table.u8, Mutability::Immutable, RefKind::Normal));
                let raw_ptr = data.create(IrTy::Ref(table.u8, Mutability::Immutable, RefKind::Raw));
                let void_ptr = data.create(IrTy::Ref(table.unit, Mutability::Immutable, RefKind::Raw));
                let str = data.create(IrTy::Ref(table.unsized_str, Mutability::Immutable, RefKind::Normal));

                CommonIrTys {
                    byte_slice,
                    ptr,
                    raw_ptr,
                    void_ptr,
                    str,
                    ..table
                }
            }
        }
    };
}

create_common_ty_table!(
    // Primitive types
    bool: IrTy::Bool,
    char: IrTy::Char,
    never: IrTy::Never,
    // Unsized string refers to the inner type of a `str`.
    //
    // @@Temporary This is only  temporary until str/[T] type semantics and rules are decided and
    // implemented.
    unsized_str: IrTy::Str,
    // Floating point types
    f32: IrTy::Float(FloatTy::F32),
    f64: IrTy::Float(FloatTy::F64),
    // Signed integer types
    i8: IrTy::Int(SIntTy::I8),
    i16: IrTy::Int(SIntTy::I16),
    i32: IrTy::Int(SIntTy::I32),
    i64: IrTy::Int(SIntTy::I64),
    i128: IrTy::Int(SIntTy::I128),
    isize: IrTy::Int(SIntTy::ISize),
    // Unsigned integer types
    u8: IrTy::UInt(UIntTy::U8),
    u16: IrTy::UInt(UIntTy::U16),
    u32: IrTy::UInt(UIntTy::U32),
    u64: IrTy::UInt(UIntTy::U64),
    u128: IrTy::UInt(UIntTy::U128),
    usize: IrTy::UInt(UIntTy::USize), // Unit types, and unit ptr types
    unit: IrTy::Adt(AdtId::UNIT),
);

/// Stores all the used [IrTy]s.
///
/// [RValue]s are accessed by an ID, of type [IrTyId].
pub struct TyStore {
    /// The map that relates [IrTyId]s to the underlying
    /// [IrTy]s.
    data: DefaultStore<IrTyId, IrTy>,

    /// Storage for grouped types, ones that appear in a parent type, i.e. a
    /// [`IrTy::Fn(...)`] type will use the [`TyListStore`] to store that
    /// parameter types.
    pub tls: TyListStore,

    /// A map of common types that are used in the IR.
    pub common_tys: CommonIrTys,
}

impl Default for TyStore {
    fn default() -> Self {
        Self::new()
    }
}

impl TyStore {
    /// Create a new [TyStore].
    pub(crate) fn new() -> Self {
        let data = DefaultStore::new();
        let tls = TyListStore::new();

        // create the common types map using the created data store
        let common_tys = CommonIrTys::new(&data);

        Self { common_tys, data, tls }
    }
}

impl Store<IrTyId, IrTy> for TyStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<IrTy>> {
        self.data.internal_data()
    }
}

impl fmt::Debug for ForFormatting<'_, IrTyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.tys().map_fast(self.item, |ty| write!(f, "{ty:?}"))
    }
}

impl fmt::Display for ForFormatting<'_, IrTyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.tys().map_fast(self.item, |ty| write!(f, "{}", ty.for_fmt(self.ctx)))
    }
}

impl fmt::Display for ForFormatting<'_, &IrTy> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            IrTy::Int(variant) => write!(f, "{variant}"),
            IrTy::UInt(variant) => write!(f, "{variant}"),
            IrTy::Float(variant) => write!(f, "{variant}"),
            IrTy::Bool => write!(f, "bool"),
            IrTy::Str => write!(f, "str"),
            IrTy::Char => write!(f, "char"),
            IrTy::Never => write!(f, "!"),
            IrTy::Ref(inner, mutability, RefKind::Normal) => {
                write!(f, "&{mutability}{}", inner.for_fmt(self.ctx))
            }
            IrTy::Ref(inner, mutability, RefKind::Raw) => {
                write!(f, "&raw {mutability}{}", inner.for_fmt(self.ctx))
            }
            IrTy::Ref(inner, mutability, RefKind::Rc) => {
                let name = match mutability {
                    Mutability::Mutable => "Mut",
                    Mutability::Immutable => "",
                };

                write!(f, "Rc{name}<{}>", inner.for_fmt(self.ctx))
            }
            IrTy::Adt(adt) => write!(f, "{}", adt.for_fmt(self.ctx)),

            IrTy::Fn { params, return_ty, .. } => {
                write!(f, "({}) -> {}", params.for_fmt(self.ctx), return_ty.for_fmt(self.ctx))
            }
            IrTy::FnDef { instance } => self.ctx.instances.map_fast(*instance, |instance| {
                write!(
                    f,
                    "{}({}) -> {}",
                    instance.name,
                    instance.params.for_fmt(self.ctx),
                    instance.ret_ty.for_fmt(self.ctx)
                )
            }),
            IrTy::Slice(ty) => write!(f, "[{}]", ty.for_fmt(self.ctx)),
            IrTy::Array { ty, length: size } => write!(f, "[{}; {size}]", ty.for_fmt(self.ctx)),
        }
    }
}

new_sequence_store_key!(pub IrTyListId);

/// Define the [TyListStore], which is a sequence of [IrTy]s associated
/// with a [IrTyListId].
pub type TyListStore = DefaultSequenceStore<IrTyListId, IrTyId>;

impl fmt::Display for ForFormatting<'_, IrTyListId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let items = self.ctx.tls().get_vec(self.item);
        let mut tys = items.iter();

        if let Some(first) = tys.next() {
            write!(f, "{first}", first = first.for_fmt(self.ctx))?;

            for ty in tys {
                write!(f, ", {ty}", ty = ty.for_fmt(self.ctx))?;
            }
        }

        Ok(())
    }
}

/// An auxiliary data structure that is used to compute the
/// [IrTy] of a [Place].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PlaceTy {
    /// The [IrTy] of the place.
    pub ty: IrTyId,

    /// If the place has been downcast, then this records
    /// the index of the variant that it has been downcast to.
    pub index: Option<VariantIdx>,
}

impl PlaceTy {
    /// Create a [PlaceTy] from a base [IrTy]. This is useful for when
    /// you want to apply a single projection on the current type
    /// and create a new [PlaceTy] from the projection.
    pub fn from_ty(ty: IrTyId) -> Self {
        Self { ty, index: None }
    }

    /// Apply a projection to the current [PlaceTy].
    fn apply_projection(self, ctx: &IrCtx, projection: PlaceProjection) -> Self {
        match projection {
            PlaceProjection::Downcast(index) => PlaceTy { ty: self.ty, index: Some(index) },
            PlaceProjection::Field(index) => {
                let ty = ctx
                    .tys()
                    .map_fast(self.ty, |ty| ty.on_field_access(index, self.index, ctx))
                    .unwrap_or_else(|| panic!("expected an ADT, got {self:?}"));

                PlaceTy { ty, index: None }
            }
            PlaceProjection::Deref => {
                let ty = ctx
                    .tys()
                    .map_fast(self.ty, |ty| ty.on_deref())
                    .unwrap_or_else(|| panic!("expected a reference, got {self:?}"));

                PlaceTy { ty, index: None }
            }
            PlaceProjection::Index(_) | PlaceProjection::ConstantIndex { .. } => {
                let ty = ctx.tys().map_fast(self.ty, |ty| ty.on_index()).unwrap_or_else(|| {
                    panic!("expected an array or slice, got `{:?}`", self.ty.for_fmt(ctx))
                });

                PlaceTy { ty, index: None }
            }
            PlaceProjection::SubSlice { from, to, from_end } => {
                let base_ty = ctx.tys().get(self.ty);
                let ty = match base_ty {
                    IrTy::Slice(_) => self.ty,
                    IrTy::Array { ty, .. } if !from_end => {
                        ctx.tys().create(IrTy::Array { ty, length: to - from })
                    }
                    IrTy::Array { ty, length: size } if from_end => {
                        ctx.tys().create(IrTy::Array { ty, length: size - from - to })
                    }
                    _ => panic!("expected an array or slice, got {self:?}"),
                };

                PlaceTy { ty, index: None }
            }
        }
    }

    /// Apply a projection on [PlaceTy] and convert it into
    /// the underlying type.
    pub fn projection_ty(self, ctx: &IrCtx, projection: PlaceProjection) -> IrTyId {
        let projected_place = self.apply_projection(ctx, projection);
        projected_place.ty
    }

    /// Create a [PlaceTy] from a [Place].
    pub fn from_place(place: Place, locals: &LocalDecls, ctx: &IrCtx) -> Self {
        // get the type of the local from the body.
        let mut base = PlaceTy { ty: locals[place.local].ty, index: None };

        ctx.projections().map_fast(place.projections, |projections| {
            for projection in projections {
                base = base.apply_projection(ctx, *projection);
            }
        });

        base
    }
}

/// This defines a trait that it used to create [IrTy]s from
/// data types that aren't defined within the IR crate, but from
/// places like the ABI where it is still useful to convert a
/// value into a [IrTy].
pub trait ToIrTy {
    /// Convert the current type into an [IrTy].
    fn to_ir_ty(&self, ctx: &IrCtx) -> IrTyId;
}

// Convert from `IntTy` into an `IrTy`.
impl ToIrTy for IntTy {
    fn to_ir_ty(&self, ctx: &IrCtx) -> IrTyId {
        match self {
            IntTy::Int(ty) => match ty {
                SIntTy::I8 => ctx.tys().common_tys.i8,
                SIntTy::I16 => ctx.tys().common_tys.i16,
                SIntTy::I32 => ctx.tys().common_tys.i32,
                SIntTy::I64 => ctx.tys().common_tys.i64,
                SIntTy::I128 => ctx.tys().common_tys.i128,
                SIntTy::ISize => ctx.tys().common_tys.isize,
                _ => unimplemented!(),
            },
            IntTy::UInt(ty) => match ty {
                UIntTy::U8 => ctx.tys().common_tys.u8,
                UIntTy::U16 => ctx.tys().common_tys.u16,
                UIntTy::U32 => ctx.tys().common_tys.u32,
                UIntTy::U64 => ctx.tys().common_tys.u64,
                UIntTy::U128 => ctx.tys().common_tys.u128,
                UIntTy::USize => ctx.tys().common_tys.usize,
                _ => unimplemented!(),
            },
        }
    }
}

impl ToIrTy for FloatTy {
    fn to_ir_ty(&self, ctx: &IrCtx) -> IrTyId {
        match self {
            FloatTy::F32 => ctx.tys().common_tys.f32,
            FloatTy::F64 => ctx.tys().common_tys.f64,
        }
    }
}

// Convert from an ABI scalar kind into an `IrTy`.
impl ToIrTy for ScalarKind {
    fn to_ir_ty(&self, ctx: &IrCtx) -> IrTyId {
        match *self {
            ScalarKind::Int { kind, signed } => {
                let int_ty = IntTy::from_integer(kind, signed);
                int_ty.to_ir_ty(ctx)
            }
            ScalarKind::Float { kind: FloatTy::F32 } => ctx.tys().common_tys.f32,
            ScalarKind::Float { kind: FloatTy::F64 } => ctx.tys().common_tys.f64,
            ScalarKind::Pointer(_) => ctx.tys().common_tys.void_ptr,
        }
    }
}
