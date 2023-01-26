//! Defines all logic regarding computing the layout of types, and
//! representing the said layouts in a way that is usable by the
//! code generation backends.

pub mod compute;
pub mod write;

use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    num::NonZeroUsize,
};

use compute::LayoutComputer;
use hash_ir::ty::{IrTy, IrTyId, ToIrTy, VariantIdx};
use hash_target::{
    abi::{AbiRepresentation, Scalar},
    alignment::Alignments,
    data_layout::{HasDataLayout, TargetDataLayout},
    primitives::{FloatTy, SIntTy, UIntTy},
    size::Size,
};
use hash_utils::{
    new_store_key,
    store::{CloneStore, DefaultStore, Store},
};
use index_vec::IndexVec;

// Define a new key to represent a particular layout.
new_store_key!(pub LayoutId);

/// A store for all of the interned [Layout]s, and a cache for
/// the [Layout]s that are created from [IrTyId]s.
pub struct LayoutCtx {
    /// The storage for all of the interned layouts
    data: DefaultStore<LayoutId, Layout>,

    /// Cache for the [Layout]s that are created from [IrTyId]s.
    cache: RefCell<HashMap<IrTyId, LayoutId>>,

    /// A reference to the [TargetDataLayout] of the current
    /// session.
    data_layout: TargetDataLayout,

    /// A table of common layouts that are used by the compiler often
    /// enough to keep in a "common" place, this avoids re-computing
    /// [Layout]s for often used types.
    pub(crate) common_layouts: CommonLayouts,
}

impl LayoutCtx {
    /// Create a new [LayoutStorage].
    pub fn new(data_layout: TargetDataLayout) -> Self {
        let data = DefaultStore::new();
        let common_layouts = CommonLayouts::new(&data_layout, &data);

        Self { data, common_layouts, cache: RefCell::new(HashMap::new()), data_layout }
    }

    /// Get a reference to the layout cache.
    pub(crate) fn cache(&self) -> Ref<HashMap<IrTyId, LayoutId>> {
        self.cache.borrow()
    }

    /// Insert a new [LayoutId] entry into the cache.
    pub(crate) fn add_cache_entry(&self, ty: IrTyId, layout: LayoutId) {
        self.cache.borrow_mut().insert(ty, layout);
    }
}

impl Store<LayoutId, Layout> for LayoutCtx {
    fn internal_data(&self) -> &RefCell<Vec<Layout>> {
        self.data.internal_data()
    }
}

macro_rules! create_common_layout_table {
    ($($name:ident: $value:expr),* $(,)?) => {
        /// Defines a map of commonly used and accessed layouts. All of the
        /// primitive types will contain a entry referring to their specific
        /// layout_id.
        pub(crate) struct CommonLayouts {
            $(pub $name: LayoutId, )*
        }

        impl CommonLayouts {
            /// Create a new [CommonLayouts] table.
            pub fn new<S: Store<LayoutId, Layout>>(data_layout: &TargetDataLayout, layouts: &S) -> Self {
                use crate::compute::compute_primitive_ty_layout;

                Self {
                    $($name: layouts.create(compute_primitive_ty_layout($value, data_layout)), )*
                }
            }
        }
    }
}

// Create common layouts for all of the primitive types
create_common_layout_table!(
    // Primitive types
    bool: IrTy::Bool,
    char: IrTy::Char,
    str: IrTy::Str,
    never: IrTy::Never,
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
    usize: IrTy::UInt(UIntTy::USize),
);

/// [TyInfo] stores a reference to the type, and a reference to the
/// layout information about the type.
#[derive(Debug, Clone, Copy)]
pub struct TyInfo {
    /// The type reference.
    pub ty: IrTyId,

    /// The layout information for the particular type.  
    pub layout: LayoutId,
}

impl TyInfo {
    /// Create a new [TyInfo] with the given type and layout.
    pub fn new(ty: IrTyId, layout: LayoutId) -> Self {
        Self { ty, layout }
    }

    /// Check if the type is a zero-sized type.
    pub fn is_zst(&self, ctx: LayoutComputer) -> bool {
        ctx.layouts().map_fast(self.layout, |layout| match layout.abi {
            AbiRepresentation::Scalar { .. }
            | AbiRepresentation::Pair(..)
            | AbiRepresentation::Vector { .. } => false,
            AbiRepresentation::Aggregate | AbiRepresentation::Uninhabited => {
                layout.size.bytes() == 0
            }
        })
    }

    /// Perform a mapping over the [IrTy] and [Layout] associated with
    /// this [LayoutWriter].
    fn with_info<F, T>(&self, ctx: &LayoutComputer, f: F) -> T
    where
        F: FnOnce(&Self, &IrTy, &Layout) -> T,
    {
        ctx.ir_ctx()
            .tys()
            .map_fast(self.ty, |ty| ctx.map_fast(self.layout, |layout| f(self, ty, layout)))
    }

    /// Compute the type of a "field with in a layout" and return the
    /// [LayoutId] associated with the field.
    pub fn field(&self, ctx: LayoutComputer, field_index: usize) -> Self {
        let ty = self.with_info(&ctx, |_, ty, layout| match ty {
            IrTy::Int(_)
            | IrTy::UInt(_)
            | IrTy::Float(_)
            | IrTy::Bool
            | IrTy::Char
            | IrTy::Never
            | IrTy::Ref(_, _, _)
            | IrTy::Fn { .. } => panic!("TyInfo::field on a type that does not contain fields"),

            IrTy::Str if field_index == 0 => ctx.ir_ctx().tys().common_tys.unit,
            IrTy::Str => ctx.ir_ctx().tys().common_tys.usize,
            IrTy::Slice(element) | IrTy::Array { ty: element, .. } => *element,
            IrTy::Adt(id) => match layout.variants {
                Variants::Single { index } => {
                    let field_ty = ctx
                        .ir_ctx()
                        .map_adt(*id, |_, adt| adt.variants[index].fields[field_index].ty);

                    field_ty
                }
                Variants::Multiple { tag, .. } => tag.kind().to_ir_ty(ctx.ir_ctx()),
            },
        });

        // If the field layout lookup created a new layout in place,
        // then we need to intern that layout here, add a cache entry
        // for it and return it, otherwise we will lookup the layout
        // buy just using the type id.
        if let Some(layout) = ctx.layouts().cache.borrow().get(&ty) {
            TyInfo { ty, layout: *layout }
        } else {
            TyInfo { ty, layout: ctx.layout_of_ty(ty).unwrap() }
        }
    }

    /// Fetch the [Layout] for a variant of the currently
    /// given [Layout].
    pub fn for_variant(&self, ctx: LayoutComputer, variant: VariantIdx) -> Self {
        let layout = ctx.layouts().get(self.layout);

        let variant = match layout.variants {
            // For enums that have only one variant that is inhabited, this
            // is represented as a single variant enum, so we need to account
            // for this situation
            Variants::Single { index }
                if index == variant && layout.shape != LayoutShape::Primitive =>
            {
                self.layout
            }
            Variants::Single { .. } => {
                let fields = ctx.ir_ctx().map_ty_as_adt(self.ty, |adt, _| {
                    if adt.variants.is_empty() {
                        panic!("layout::for_variant called on a zero-variant enum")
                    }

                    adt.variant(variant).fields.len()
                });

                // Create a new layout with basically a ZST that is
                // un-inhabited... i.e. `never` or create a union across
                // all of the variant fields.
                let shape = match NonZeroUsize::new(fields) {
                    Some(fields) => LayoutShape::Union { count: fields },
                    None => LayoutShape::Aggregate { fields: vec![], memory_map: vec![] },
                };

                ctx.layouts().create(Layout::new(
                    shape,
                    Variants::Single { index: variant },
                    AbiRepresentation::Uninhabited,
                    ctx.data_layout().i8_align,
                    Size::ZERO,
                ))
            }

            // @@Verify: should we copy the layout of the variant here?
            Variants::Multiple { ref variants, .. } => variants[variant],
        };

        Self::new(self.ty, variant)
    }
}

/// Represents the [Layout] of a particular type in Hash. This captures
/// all possible kinds of type, including primitives, structs, enums, etc.
///
/// The [Layout] contains a `shape` which stores fields that are shared
/// across all *variants* (if the type has multiple variants), and a
/// [Variants] enum which stores information about the variants of the type.
#[derive(Debug, Clone)]

pub struct Layout {
    /// The shape of the layout, this stores information about
    /// where fields are located, their order, padding, etc.
    pub shape: LayoutShape,

    /// Represents layout information for types that have
    /// multiple variants
    pub variants: Variants,

    /// Denotes how this layout value is represented in the ABI.
    pub abi: AbiRepresentation,

    /// Specified alignments by the ABI and a "preferred" alignment.
    pub alignment: Alignments,

    /// The size of the layout.
    pub size: Size,
}

impl Layout {
    /// Create a new layout with the given information.
    pub fn new(
        shape: LayoutShape,
        variants: Variants,
        abi: AbiRepresentation,
        alignment: Alignments,
        size: Size,
    ) -> Self {
        Self { shape, variants, abi, alignment, size }
    }

    /// Create a new [Layout] that represents a scalar.
    pub fn scalar<C: HasDataLayout>(ctx: &C, scalar: Scalar) -> Self {
        let size = scalar.size(ctx);
        let alignment = scalar.align(ctx);

        Self {
            shape: LayoutShape::Primitive,
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi: AbiRepresentation::Scalar(scalar),
            alignment,
            size,
        }
    }

    /// Create a new [Layout] that represents a scalar pair.
    pub fn scalar_pair<C: HasDataLayout>(ctx: &C, scalar_1: Scalar, scalar_2: Scalar) -> Self {
        let dl = ctx.data_layout();

        let scalar_1_size = scalar_1.size(ctx);
        let scalar_2_size = scalar_2.size(ctx);

        let alignment_2 = scalar_2.align(ctx);

        // Take the maximum of `scalar_1`, `scalar_2` and the `aggregate` target
        // alignment
        let alignment = scalar_1.align(ctx).max(alignment_2).max(dl.aggregate_align);

        let offset_2 = scalar_1_size.align_to(alignment.abi);
        let size = (offset_2 + scalar_2_size).align_to(alignment.abi);

        Layout {
            shape: LayoutShape::Aggregate {
                fields: vec![
                    FieldLayout { size: scalar_1_size, offset: Size::ZERO },
                    FieldLayout { size: scalar_2_size, offset: offset_2 },
                ],
                memory_map: vec![0, 1],
            },
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi: AbiRepresentation::Pair(scalar_1, scalar_2),
            alignment,
            size,
        }
    }

    /// Check whether this particular [Layout] represents a zero-sized type.
    pub fn is_zst(&self) -> bool {
        match self.abi {
            AbiRepresentation::Scalar { .. }
            | AbiRepresentation::Pair(..)
            | AbiRepresentation::Vector { .. } => false,
            AbiRepresentation::Aggregate | AbiRepresentation::Uninhabited => self.size.bytes() == 0,
        }
    }
}

/// Represents the shape of the [Layout] for the fields. All layouts
/// are either represented as a "primitive" (scalar values like `i32`, `u8`,
/// etc), an array with a known size (which isn't supported in the language
/// yet), or a `struct`-like type.
///
/// For [`LayoutShape::Aggregate`], there are two maps stored, the first being
/// all of the field **offset**s in "source" definition order, and a
/// `memory_map` which specifies the actual order of fields in memory in
/// relation to their offsets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutShape {
    /// Primitives, `!` and other scalar-like types have only one specific
    /// layout.
    Primitive,

    /// A `union` like layout, all of the fields begin at the
    /// start of the layout, and the size of the layout is the
    /// size of the largest field.
    Union { count: NonZeroUsize },

    /// Layout for array/vector like types that have a known element
    /// count at compile time.
    Array {
        /// The size of each element in the array layout.
        stride: Size,

        /// The number of elements in the array layout.
        elements: u64,
    },

    /// Layout for aggregate types. The layout contains a collection of fields
    /// with specified offsets.
    ///
    /// Fields of the `struct`-like type are guaranteed to never overlap, and
    /// gaps between fields are either padding between a field, or space left
    /// over to denote a **discriminant** alignment (in the case of `enum`s).
    Aggregate {
        /// Offsets of the the first byte of each field in the struct. This
        /// is in the "source order" of the `struct`-like type.
        fields: Vec<FieldLayout>,

        /// A map between the specified "source order" of the fields, and
        /// the actual order in memory.
        memory_map: Vec<u32>,
    },
}

/// [FieldLayout] represents the details of a "field" within an
/// aggregate data layout. This is used to store the offset of the
/// field within the layout, and the "true" [Size] of the field. The
/// term "true" is used to denote that the size of the field may be
/// smaller due to introduced padding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldLayout {
    /// The offset of the field within the layout.
    pub offset: Size,

    /// The size of the field itself.
    pub size: Size,
}

impl FieldLayout {
    /// Create a [FieldLayout] that represents a ZST.
    pub fn zst() -> Self {
        Self { offset: Size::ZERO, size: Size::ZERO }
    }
}

impl LayoutShape {
    /// Count the number of fields in the [LayoutShape].
    #[inline]
    pub fn count(&self) -> usize {
        match *self {
            LayoutShape::Primitive => 1,
            LayoutShape::Union { count } => count.get(),
            LayoutShape::Array { elements, .. } => elements.try_into().unwrap(),
            LayoutShape::Aggregate { fields: ref offsets, .. } => offsets.len(),
        }
    }

    /// Get a specific `offset` from the [LayoutShape], and given an
    /// index into the layout.
    #[inline]
    pub fn offset(&self, index: usize) -> Size {
        match *self {
            LayoutShape::Primitive => unreachable!("primitive layout has no defined offsets"),
            LayoutShape::Union { .. } => Size::ZERO,
            LayoutShape::Array { stride, elements } => {
                let index = index as u64;
                assert!(index < elements);
                stride * index
            }
            LayoutShape::Aggregate { ref fields, .. } => fields[index].offset,
        }
    }

    /// Get the memory index of a specific field in the layout shape, and given
    /// an a "source order" index into the layout. This is used to get the
    /// actual memory order of a field in the layout.
    pub fn memory_index(&self, index: usize) -> usize {
        match self {
            LayoutShape::Primitive => unreachable!("primitive layout has no defined offsets"),
            LayoutShape::Union { .. } | LayoutShape::Array { .. } => index,
            LayoutShape::Aggregate { memory_map, .. } => memory_map[index] as usize,
        }
    }

    /// Iterate over offsets in the [LayoutShape] by increasing offsets.
    pub fn iter_increasing_offsets(&self) -> impl Iterator<Item = usize> + '_ {
        let mut inverse = vec![0; self.count()];

        // iterate over the memory map and create the inverse map
        // for the fields in the layout.
        if let LayoutShape::Aggregate { memory_map, .. } = self {
            for (i, &index) in memory_map.iter().enumerate() {
                inverse[index as usize] = i;
            }
        }

        (0..self.count()).map(move |i| match *self {
            LayoutShape::Primitive | LayoutShape::Union { .. } | LayoutShape::Array { .. } => i,
            LayoutShape::Aggregate { .. } => inverse[i],
        })
    }
}

/// Represents the layout of a type that has multiple variants. If the
/// [Layout] has a single variant, then the [Variants] will be a
/// [`Variants::Single`].
#[derive(Clone, Debug)]
pub enum Variants {
    /// A single variant, tuples, structs, non-ADTs or univariant `enum`s.
    Single { index: VariantIdx },

    /// Multiple variants, `enum`s with multiple variants.
    ///
    /// Each variant comes with a discriminant value, and there
    /// is reserved space within the layout of each variant to
    /// store the tag. The tag is always located in the same
    /// position within the type layout.
    Multiple {
        /// The type of the tag that is used to represent the discriminant.
        tag: Scalar,

        /// The position of the field that is used to determine which
        /// discriminant is active.
        field: usize,

        /// The layout of all of the variants
        variants: IndexVec<VariantIdx, LayoutId>,
    },
}
