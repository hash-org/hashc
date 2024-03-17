//! A type representation that is used in all areas of the compiler except the
//! TIR.

use std::{
    cmp,
    fmt::{self, Debug},
};

use hash_ast::ast;
use hash_reporting::macros::panic_on_span;
use hash_source::{
    constant::{FloatTy, IntTy, SIntTy, UIntTy},
    identifier::Identifier,
    SourceId,
};
use hash_storage::{
    static_sequence_store_indirect, static_single_store,
    store::{
        statics::{SingleStoreValue, StoreId},
        SequenceStore,
    },
};
use hash_target::{
    abi::{self, Abi, Integer, ScalarKind},
    data_layout::HasDataLayout,
    discriminant::Discriminant,
    primitives::BigIntTy,
    size::Size,
};
use hash_utils::{
    bitflags::bitflags,
    index_vec::{self, index_vec, IndexVec},
    lazy_static,
};

use crate::repr_stores;

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

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// A function type, contains the types of the parameters and the
/// return type of the function.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FnTy {
    /// A reference to the parameter types of this function
    /// instance.
    pub params: ReprTyListId,

    /// The function return type.
    pub return_ty: ReprTyId,
    // @@Todo: do we need to keep around an AstNodeId for the attributes?
}

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
    pub params: ReprTyListId,

    /// The function return type.
    pub return_ty: ReprTyId,

    /// Any attributes that are present  on the instance, this is used
    /// to specify special behaviour of the function.
    pub attr_id: ast::AstNodeId,

    /// The source of this function instance. This is useful
    /// for when symbol names are mangled, and we need to
    /// include a reference to where it was defined.
    ///
    /// @@Future: Ideally, this information should deduce a namespaced
    /// path to the module location instead of just using the module
    /// id as the disambiguator.
    pub source: Option<SourceId>,

    /// The ABI of the function, defaults to [`Abi::Hash`].
    ///
    /// @@Future: introduce `#extern "<abi>"` syntax, but this involves adding
    /// directives with arguments.
    pub abi: Abi,

    /// If the instance refers to an intrinsic function, and will be converted
    /// into possibly some different code.
    pub is_intrinsic: bool,

    /// If the function instance originates from a generic function.
    polymoprhpic_origin: bool,
}

impl Instance {
    /// Create a new instance.
    pub fn new(
        name: Identifier,
        source: Option<SourceId>,
        params: ReprTyListId,
        return_ty: ReprTyId,
        attr_id: ast::AstNodeId,
    ) -> Self {
        Self {
            name,
            is_intrinsic: false,
            params,
            source,
            return_ty,
            polymoprhpic_origin: false,
            abi: Abi::Hash,
            attr_id,
        }
    }

    /// Get the name from the instance.
    pub fn name(&self) -> Identifier {
        self.name
    }

    /// Check if the instance is of a generic origin.
    pub fn is_origin_polymorphic(&self) -> bool {
        self.polymoprhpic_origin
    }

    /// Check if the [Instance] is an intrinsic function.
    pub fn is_intrinsic(&self) -> bool {
        self.is_intrinsic
    }
}

static_single_store!(
    store = pub InstanceStore,
    id = pub InstanceId,
    value = Instance,
    store_name = instances,
    store_source = repr_stores(),
    derives = Debug
);

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
pub enum ReprTy {
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
    Ref(ReprTyId, Mutability, RefKind),

    /// A slice type, `&[T]`.
    Slice(ReprTyId),

    /// An array type with a specified length, i.e. `[T; N]`
    Array { ty: ReprTyId, length: usize },

    /// An abstract data structure type, i.e a `struct` or `enum`, or any
    /// other kind of type.
    Adt(AdtId),

    /// A function type, with interned parameter type list and a return
    /// type.
    Fn(FnTy),

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

impl ReprTy {
    /// Make a tuple type, i.e. `(T1, T2, T3, ...)`
    pub fn tuple(tys: &[ReprTyId]) -> ReprTy {
        let variants = index_vec![AdtVariant::singleton(
            Identifier::num(0),
            tys.iter()
                .copied()
                .enumerate()
                .map(|(idx, ty)| AdtField { name: Identifier::num(idx), ty })
                .collect(),
        )];
        let adt = Adt::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
        Self::Adt(Adt::create(adt))
    }

    pub fn make_tuple(tys: &[ReprTyId]) -> ReprTyId {
        ReprTy::create(ReprTy::tuple(tys))
    }

    /// Create a reference type to the provided [ReprTy].
    pub fn make_ref(ty: ReprTy, mutability: Mutability, kind: RefKind) -> ReprTyId {
        Self::create(Self::Ref(Self::create(ty), mutability, kind))
    }

    /// Check if a type is a reference type.
    pub fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_, _, _))
    }

    /// Check if the [ReprTy] is an integral type.
    pub fn is_integral(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_))
    }

    /// Assert that the type is an integral one.
    pub fn as_int(&self) -> IntTy {
        match self {
            Self::Int(ty) => IntTy::Int(*ty),
            Self::UInt(ty) => IntTy::UInt(*ty),
            _ => unreachable!(), // @@Todo: handle big ints?
        }
    }

    /// Check whether the [ReprTy] is "switchable", as in if
    /// it can be compared without any additional work. This
    /// is primarily used for generating code for `match` statements.
    pub fn is_switchable(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_) | Self::Char | Self::Bool)
    }

    /// Check if the [ReprTy] is a floating point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float(_))
    }

    /// Check if the [ReprTy] is a signed integral type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Check if a [ReprTy] is a function type.
    pub fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    /// Check if a [ReprTy] is a function type.
    pub fn is_fn_def(&self) -> bool {
        matches!(self, Self::FnDef { .. })
    }

    /// Check if a type is a scalar, i.e. it cannot be divided into
    /// further components. [`ReprTy::Ref(..)`] with non-[`RefKind::Rc`] is also
    /// considered as a scalar since the components of the reference are
    /// *opaque* to the compiler because it isn't managed.
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            Self::Int(_)
                | Self::UInt(_)
                | Self::Float(_)
                | Self::Char
                | Self::Bool)

            // A reference to `str` is non-scalar since it is a fat pointer.
            || matches!(self, Self::Ref(element, _, RefKind::Normal | RefKind::Raw) if element.is_str())
    }

    /// Check if the type is an array.
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array { .. })
    }

    pub fn is_str(&self) -> bool {
        matches!(self, Self::Str)
    }

    /// Check if the type is an ADT.
    pub fn is_adt(&self) -> bool {
        matches!(self, Self::Adt(_))
    }

    /// Assuming that the [ReprTy] is an ADT, return the [AdtId]
    /// of the underlying ADT.
    pub fn as_adt(&self) -> AdtId {
        match self {
            Self::Adt(adt_id) => *adt_id,
            ty => panic!("expected ADT, but got {ty:?}"),
        }
    }

    /// Assuming that the [ReprTy] is an function definition, return the
    /// [InstanceId] of the underlying function definition.
    pub fn as_instance(&self) -> InstanceId {
        match self {
            Self::FnDef { instance } => *instance,
            ty => panic!("expected fn def, but got {ty:?}"),
        }
    }

    /// Assuming that the [ReprTy] is a function type, return the [FnTy].
    pub fn as_fn(&self) -> FnTy {
        match self {
            Self::Fn(ty) => *ty,
            ty => panic!("expected function type, but got {ty:?}"),
        }
    }

    /// Get the type of this [ReprTy] if a dereference is performed on it.
    pub fn on_deref(&self) -> Option<ReprTyId> {
        match self {
            Self::Ref(ty, _, _) => Some(*ty),
            _ => None,
        }
    }

    /// Get the type of this [ReprTy] if an index operation
    /// is performed on it.
    pub fn on_index(&self) -> Option<ReprTyId> {
        match self {
            Self::Slice(ty) | Self::Array { ty, .. } => Some(*ty),
            _ => None,
        }
    }

    /// Get the type of this [ReprTy] if a field access is performed on it.
    /// Optionally, the function can be supplied a [VariantIdx] in order to
    /// access a particular variant of the ADT (for `enum`s and `union`s).
    pub fn on_field_access(&self, field: usize, variant: Option<VariantIdx>) -> Option<ReprTyId> {
        match self {
            ReprTy::Adt(id) => id.map(|adt| {
                let variant = match variant {
                    Some(variant) => adt.variant(variant),
                    None => adt.univariant(),
                };

                Some(variant.field(field).ty)
            }),
            _ => None,
        }
    }

    /// Compute the discriminant value for a particular [ReprTy] and
    /// evaluate it to a raw value.
    pub fn discriminant_for_variant(&self, variant: VariantIdx) -> Option<(IntTy, u128)> {
        match self {
            ReprTy::Adt(id) => {
                if !id.borrow().flags.is_enum() || id.borrow().variants.is_empty() {
                    None
                } else {
                    let (discriminant_value, discriminant_type) =
                        id.map(|def| (def.discriminant_value_for(variant), def.discriminant_ty()));

                    Some((discriminant_type, discriminant_value))
                }
            }
            _ => None,
        }
    }

    /// Compute the discriminant type for the given type. This computes
    /// the specific "discriminant" for `enum` ADTs, and simply returns a
    /// `u8` for all other types. This is because the discriminant type of
    /// all other types is considered to be `0`, and thus a `u8` is sufficient.
    pub fn discriminant_ty(&self) -> ReprTyId {
        match self {
            ReprTy::Adt(id) => {
                if id.borrow().flags.is_enum() {
                    id.borrow().discriminant_ty().to_repr_ty()
                } else {
                    COMMON_REPR_TYS.u8
                }
            }
            ReprTy::Int(_)
            | ReprTy::UInt(_)
            | ReprTy::Float(_)
            | ReprTy::Str
            | ReprTy::Bool
            | ReprTy::Char
            | ReprTy::Never
            | ReprTy::Ref(_, _, _)
            | ReprTy::Slice(_)
            | ReprTy::Array { .. }
            | ReprTy::FnDef { .. }
            | ReprTy::Fn { .. } => COMMON_REPR_TYS.u8,
        }
    }

    /// Attempt to compute the type of an element from an [`ReprTy::Slice`] or
    /// [`ReprTy::Array`]. If the type is not a slice or array, then `None` is
    /// returned.
    pub fn element_ty(&self) -> Option<ReprTyId> {
        match self {
            ReprTy::Slice(ty) | ReprTy::Array { ty, .. } => Some(*ty),
            ReprTy::Ref(ty, _, _) => ty.borrow().element_ty(),
            _ => None,
        }
    }
}

impl From<ReprTy> for IntTy {
    fn from(ty: ReprTy) -> Self {
        match ty {
            ReprTy::Int(ty) => Self::Int(ty),
            ReprTy::UInt(ty) => Self::UInt(ty),
            _ => panic!("expected integral type, but got {ty:?}"),
        }
    }
}

impl From<ReprTyId> for IntTy {
    fn from(ty: ReprTyId) -> Self {
        ty.value().into()
    }
}

impl From<ReprTy> for FloatTy {
    fn from(ty: ReprTy) -> Self {
        match ty {
            ReprTy::Float(ty) => ty,
            _ => panic!("expected float type, but got {ty:?}"),
        }
    }
}

impl From<ReprTyId> for FloatTy {
    fn from(ty: ReprTyId) -> Self {
        ty.value().into()
    }
}

static_single_store!(
    store = pub ReprTyStore,
    id = pub ReprTyId,
    value = ReprTy,
    store_name = tys,
    store_source = repr_stores(),
    derives = Debug
);

impl ReprTyId {
    /// Check if the type is an integral.
    pub fn is_integral(&self) -> bool {
        self.borrow().is_integral()
    }

    /// Check if the type is a float.
    pub fn is_float(&self) -> bool {
        self.borrow().is_float()
    }

    /// Check if the type is a signed integer.
    pub fn is_signed(&self) -> bool {
        self.borrow().is_signed()
    }

    /// Check if the type is a raw `str` type.
    pub fn is_str(&self) -> bool {
        self.borrow().is_str()
    }

    /// Check if the type is a function definition type.
    pub fn is_fn_def(&self) -> bool {
        self.borrow().is_fn_def()
    }
}

static_sequence_store_indirect!(
    store = pub ReprTyListStore,
    id = pub ReprTyListId[ReprTyId],
    store_name = ty_list,
    store_source = repr_stores()
);

impl ReprTyListId {
    pub fn seq<I: IntoIterator<Item = ReprTyId>>(values: I) -> Self {
        repr_stores().ty_list().create_from_iter(values)
    }
}

/// Macro that is used to create the "common" IR types. Each
/// entry has an associated name, and then followed by the type
/// expression that represents the [ReprTy].
macro_rules! create_common_ty_table {
    ($($name:ident: $value:expr),* $(,)?) => {

        /// Defines a map of common types that might be used in the IR
        /// and general IR operations. When creating new types that refer
        /// to these common types, they should be created using the
        /// using the associated [ReprTyId]s of this map.
        pub struct CommonReprTys {
            $(pub $name: ReprTyId, )*
        }

        impl CommonReprTys {
            pub fn new() -> CommonReprTys {
                // Create a `unit` type in order to reserve the first index of
                // the ADT for a `()` type.
                let _ = ReprTy::tuple(&[]);
                $(let $name = ReprTy::create($value); )*

                CommonReprTys {
                    $($name,)*
                }
            }
        }

        impl Default for CommonReprTys {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

create_common_ty_table!(
    // ------------------------------------------
    // Primitive types
    // ------------------------------------------
    bool: ReprTy::Bool,
    char: ReprTy::Char,
    never: ReprTy::Never,

    // ------------------------------------------
    // Floating point types
    // ------------------------------------------
    f32: ReprTy::Float(FloatTy::F32),
    f64: ReprTy::Float(FloatTy::F64),

    // ------------------------------------------
    // Signed integer types
    // ------------------------------------------
    i8: ReprTy::Int(SIntTy::I8),
    i16: ReprTy::Int(SIntTy::I16),
    i32: ReprTy::Int(SIntTy::I32),
    i64: ReprTy::Int(SIntTy::I64),
    i128: ReprTy::Int(SIntTy::I128),
    isize: ReprTy::Int(SIntTy::ISize),

    // ------------------------------------------
    // Unsigned integer types
    // ------------------------------------------
    u8: ReprTy::UInt(UIntTy::U8),
    u16: ReprTy::UInt(UIntTy::U16),
    u32: ReprTy::UInt(UIntTy::U32),
    u64: ReprTy::UInt(UIntTy::U64),
    u128: ReprTy::UInt(UIntTy::U128),

    // ------------------------------------------
    // Unit types, and unit ptr types
    // ------------------------------------------
    usize: ReprTy::UInt(UIntTy::USize),
    unit: ReprTy::Adt(AdtId::UNIT),

    // ------------------------------------------
    // BigInts
    // ------------------------------------------
    ubig: ReprTy::Slice(u64),
    ibig: ReprTy::tuple(&[bool, ubig]),

    // ------------------------------------------
    // Pointer types
    // ------------------------------------------
    byte_slice: ReprTy::Slice(u8),
    ptr: ReprTy::Ref(u8, Mutability::Immutable, RefKind::Normal),
    raw_ptr: ReprTy::Ref(u8, Mutability::Immutable, RefKind::Raw),
    void_ptr: ReprTy::Ref(unit, Mutability::Immutable, RefKind::Raw),
    unsized_str: ReprTy::Str,
    str: ReprTy::Ref(unsized_str, Mutability::Immutable, RefKind::Normal),
);

lazy_static::lazy_static!(
    pub static ref COMMON_REPR_TYS: CommonReprTys = CommonReprTys::new();
);

impl fmt::Display for ReprTyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map(|ty| write!(f, "{}", ty))
    }
}

impl fmt::Display for &ReprTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReprTy::Int(variant) => write!(f, "{variant}"),
            ReprTy::UInt(variant) => write!(f, "{variant}"),
            ReprTy::Float(variant) => write!(f, "{variant}"),
            ReprTy::Bool => write!(f, "bool"),
            ReprTy::Str => write!(f, "str"),
            ReprTy::Char => write!(f, "char"),
            ReprTy::Never => write!(f, "!"),
            ReprTy::Ref(inner, mutability, RefKind::Normal) => {
                write!(f, "&{mutability}{}", inner)
            }
            ReprTy::Ref(inner, mutability, RefKind::Raw) => {
                write!(f, "&raw {mutability}{}", inner)
            }
            ReprTy::Ref(inner, mutability, RefKind::Rc) => {
                let name = match mutability {
                    Mutability::Mutable => "Mut",
                    Mutability::Immutable => "",
                };

                write!(f, "Rc{name}<{}>", inner)
            }
            ReprTy::Adt(adt) => write!(f, "{}", adt),

            ReprTy::Fn(FnTy { params, return_ty, .. }) => {
                write!(f, "({}) -> {}", params, return_ty)
            }
            ReprTy::FnDef { instance } => {
                write!(f, "{}", instance.borrow().name)
            }
            ReprTy::Slice(ty) => write!(f, "[{}]", ty),
            ReprTy::Array { ty, length: size } => write!(f, "[{}; {size}]", ty),
        }
    }
}

// new_sequence_store_key_indirect!(pub ReprTyListId, ReprTyId, derives =
// Debug);

/// Define the [TyListStore], which is a sequence of [ReprTy]s associated
/// with a [ReprTyListId].
// pub type TyListStore = DefaultSequenceStore<ReprTyListId, ReprTyId>;

impl fmt::Display for ReprTyListId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = self.value();
        let mut tys = value.iter();

        if let Some(first) = tys.next() {
            write!(f, "{first}")?;

            for ty in tys {
                write!(f, ", {ty}")?;
            }
        }

        Ok(())
    }
}

/// An auxiliary data structure that is used to compute the
/// [ReprTy] of a [Place].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PlaceTy {
    /// The [ReprTy] of the place.
    pub ty: ReprTyId,

    /// If the place has been downcast, then this records
    /// the index of the variant that it has been downcast to.
    pub index: Option<VariantIdx>,
}

/// This defines a trait that it used to create [ReprTy]s from
/// data types that aren't defined within the IR crate, but from
/// places like the ABI where it is still useful to convert a
/// value into a [ReprTy].
pub trait ToReprTy {
    /// Convert the current type into an [ReprTy].
    fn to_repr_ty(&self) -> ReprTyId;
}

// Convert from `IntTy` into an `ReprTy`.
impl ToReprTy for IntTy {
    fn to_repr_ty(&self) -> ReprTyId {
        match self {
            IntTy::Int(ty) => match ty {
                SIntTy::I8 => COMMON_REPR_TYS.i8,
                SIntTy::I16 => COMMON_REPR_TYS.i16,
                SIntTy::I32 => COMMON_REPR_TYS.i32,
                SIntTy::I64 => COMMON_REPR_TYS.i64,
                SIntTy::I128 => COMMON_REPR_TYS.i128,
                SIntTy::ISize => COMMON_REPR_TYS.isize,
            },
            IntTy::UInt(ty) => match ty {
                UIntTy::U8 => COMMON_REPR_TYS.u8,
                UIntTy::U16 => COMMON_REPR_TYS.u16,
                UIntTy::U32 => COMMON_REPR_TYS.u32,
                UIntTy::U64 => COMMON_REPR_TYS.u64,
                UIntTy::U128 => COMMON_REPR_TYS.u128,
                UIntTy::USize => COMMON_REPR_TYS.usize,
            },
            IntTy::Big(ty) => match ty {
                BigIntTy::IBig => COMMON_REPR_TYS.ibig,
                BigIntTy::UBig => COMMON_REPR_TYS.ubig,
            },
        }
    }
}

impl ToReprTy for FloatTy {
    fn to_repr_ty(&self) -> ReprTyId {
        match self {
            FloatTy::F32 => COMMON_REPR_TYS.f32,
            FloatTy::F64 => COMMON_REPR_TYS.f64,
        }
    }
}

// Convert from an ABI scalar kind into an `ReprTy`.
impl ToReprTy for ScalarKind {
    fn to_repr_ty(&self) -> ReprTyId {
        match *self {
            ScalarKind::Int { kind, signed } => {
                let int_ty = IntTy::from_integer(kind, signed);
                int_ty.to_repr_ty()
            }
            ScalarKind::Float { kind: FloatTy::F32 } => COMMON_REPR_TYS.f32,
            ScalarKind::Float { kind: FloatTy::F64 } => COMMON_REPR_TYS.f64,
            ScalarKind::Pointer(_) => COMMON_REPR_TYS.void_ptr,
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
pub struct Adt {
    /// The name of the ADT
    pub name: Identifier,

    /// All of the variants that are defined for this variant.
    pub variants: IndexVec<VariantIdx, AdtVariant>,

    /// An origin node, this is specified if this is a
    /// type created from a type definition in source.
    pub origin: Option<ast::AstNodeId>,

    /// Any type substitutions that appeared when the type was
    /// lowered. This is not important for the type itself, but for
    /// printing the type, and computing the name of the type does
    /// depend on this information.
    pub substitutions: Option<ReprTyListId>,

    // Flags which denote additional information about this specific
    // data structure.
    pub flags: AdtFlags,

    /// Options that are regarding the representation of the ADT
    /// in memory.
    pub metadata: AdtRepresentation,
}

impl Adt {
    /// Create a new [AdtData] with the given name and variants.
    pub fn new(name: Identifier, variants: IndexVec<VariantIdx, AdtVariant>) -> Self {
        Self {
            name,
            variants,
            metadata: AdtRepresentation::default(),
            flags: AdtFlags::empty(),
            substitutions: None,
            origin: None,
        }
    }

    /// Create [Adt] with specified [AdtFlags].
    pub fn new_with_flags(
        name: Identifier,
        variants: IndexVec<VariantIdx, AdtVariant>,
        flags: AdtFlags,
    ) -> Self {
        Self {
            name,
            variants,
            metadata: AdtRepresentation::default(),
            flags,
            substitutions: None,
            origin: None,
        }
    }

    /// Get the origin of the ADT, if it exists.
    pub fn origin(&self) -> Option<ast::AstNodeId> {
        self.origin
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
    pub fn discriminant_ty(&self) -> IntTy {
        debug_assert!(self.flags.is_enum() || self.flags.is_union());

        if let Some(ty) = self.metadata.discriminant {
            return ty;
        }

        // Compute the maximum number of bits needed for the discriminant.
        let max = self.variants.len() as u64;
        let bits = max.leading_zeros();
        let size = Size::from_bits(cmp::max(1, 64 - bits));

        IntTy::UInt(UIntTy::from_size(size))
    }

    /// Compute the representation of the discriminant of this [Adt]
    /// in terms of a [abi::Integer]. Getting the discriminant representation
    /// uses the following rules:
    ///
    /// - If the `repr` attribute specifies a discriminant, then we use that.
    ///
    /// - We determine the "minimum" size of the discriminant by using the
    ///   rules:
    ///
    ///    - If the ADT is a C-like type, then we use the minimum size specified
    ///      by the target, i.e. `c_style_enum_min_size` in the data layout.
    ///
    ///    - default to using a `u8`.
    ///
    /// - Using the minimum, we then determine the "fit" of the discriminant by
    ///   computing the maximum discriminant value, and then determining the
    ///   smallest integer type that can fit that value.
    pub fn discriminant_representation<C: HasDataLayout>(
        &self,
        ctx: &C,
        min: i128,
        max: i128,
    ) -> (abi::Integer, bool) {
        let unsigned_fit = Integer::fit_unsigned(cmp::max(min as u128, max as u128));
        let signed_fit = cmp::max(Integer::fit_signed(min), Integer::fit_signed(max));

        // If this representation specifies a `repr`, then we default to using that,
        // otherwise we fallback on trying to compute the size of the discriminant.
        if let Some(discr_ty) = self.metadata.discriminant {
            let discr = abi::Integer::from_int_ty(discr_ty, ctx);
            let fit = if discr_ty.is_signed() { signed_fit } else { unsigned_fit };

            // Ensure that the discr fits the fit.
            if discr < fit {
                panic_on_span!(self.origin().unwrap().span(), format!("Specified discriminant type is too small for the discriminant range of the enum, fit={fit:?}, specified={discr:?}"))
            }

            return (discr, discr_ty.is_signed());
        }

        // The user did not specify the representation, or no representation was deduced
        // from the attributes, so we compute the discriminant size using the documented
        // rules.

        // If this is a C-like representation, then we always
        // default to the tag enum size specified by the target.
        let minimum = if self.metadata.is_c_like() {
            ctx.data_layout().c_style_enum_min_size
        } else {
            Integer::I8
        };

        // @@Todo: actually get the signedness of the discriminant, we would have to
        // compute the type of the discriminant, and then check if any of the the
        // discriminant values are less than zero.
        if min >= 0 {
            (cmp::max(unsigned_fit, minimum), false)
        } else {
            (cmp::max(signed_fit, minimum), true)
        }
    }

    /// Compute the discriminant value for a particular variant.
    pub fn discriminant_value_for(&self, variant: VariantIdx) -> u128 {
        debug_assert!(self.flags.is_enum());
        self.variants[variant].discriminant.value
    }

    /// Create an iterator of all of the discriminants of this ADT.
    pub fn discriminants(&self) -> impl Iterator<Item = (VariantIdx, u128)> + '_ {
        self.variants.indices().map(|idx| (idx, self.variants[idx].discriminant.value))
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
    /// Whether to use a specific type for the discriminant.
    pub discriminant: Option<IntTy>,

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

    /// The discriminant value of this variant.
    pub discriminant: Discriminant,
}

impl AdtVariant {
    /// Make a singleton variant, implicitly setting the discriminant value
    /// as being `0`.
    pub fn singleton(name: Identifier, fields: Vec<AdtField>) -> Self {
        Self { name, fields, discriminant: Discriminant::initial(IntTy::Int(SIntTy::ISize)) }
    }

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
    pub ty: ReprTyId,
}

static_single_store!(
    store = pub AdtStore,
    id = pub AdtId,
    value = Adt,
    store_name = adts,
    store_source = repr_stores(),
    derives = Debug
);

impl AdtId {
    /// The unit type always uses the first ID in the store.
    pub const UNIT: AdtId = AdtId { index: 0 };
}

impl fmt::Display for AdtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map(|adt| write!(f, "{}", adt))
    }
}

impl fmt::Display for &Adt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.flags {
            AdtFlags::TUPLE => {
                assert!(self.variants.len() == 1);
                let variant = &self.variants[0];

                write!(f, "(")?;
                for (i, field) in variant.fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", field.ty)?;
                }

                write!(f, ")")
            }
            _ => {
                // We just write the name of the underlying ADT
                write!(f, "{}", self.name)?;

                // If there are type arguments, then we write them
                // out as well.
                if let Some(args) = self.substitutions {
                    write!(f, "<")?;

                    for (i, arg) in args.borrow().iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }

                        write!(f, "{}", arg)?;
                    }

                    write!(f, ">")?;
                }

                Ok(())
            }
        }
    }
}
