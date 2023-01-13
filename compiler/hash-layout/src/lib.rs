//! Defines all logic regarding computing the layout of types, and
//! representing the said layouts in a way that is usable by the
//! code generation backends.

pub mod compute;

use std::num::NonZeroUsize;

use hash_ir::{
    ty::{IrTy, IrTyId, VariantIdx},
    IrCtx,
};
use hash_target::{
    abi::{AbiRepresentation, Scalar},
    alignment::Alignments,
    layout::{HasDataLayout, TargetDataLayout},
    primitives::{FloatTy, SIntTy, UIntTy},
    size::Size,
};
use hash_utils::{
    new_store, new_store_key,
    store::{CloneStore, Store},
};
use index_vec::IndexVec;

// Define a new key to represent a particular layout.
new_store_key!(pub LayoutId);

// Storage for all of the generated layouts.
new_store!(
    pub LayoutStore<LayoutId, Layout>
);

/// A auxialliary context for methods defined on [Layout]
/// which require access to other [Layout]s and information
/// generated in the [IrCtx].
pub struct LayoutCtx<'abi> {
    /// A reference tot the [LayoutStore].
    layouts: &'abi LayoutStore,

    /// A reference to the [IrCtx].
    ir_ctx: &'abi IrCtx,

    /// A reference to the [TargetDataLayout] of the current
    /// session.
    data_layout: &'abi TargetDataLayout,

    /// A table of common layouts that are used by the compiler often
    /// enough to keep in a "common" place, this also avoids re-making
    /// alot of layouts for the same frequent typs.
    pub(crate) common_layouts: CommonLayouts,
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
            pub fn new(data_layout: &TargetDataLayout, layouts: &LayoutStore) -> Self {
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

impl<'abi> LayoutCtx<'abi> {
    /// Create a new [LayoutCtx].
    pub fn new(
        layouts: &'abi LayoutStore,
        data_layout: &'abi TargetDataLayout,
        ir_ctx: &'abi IrCtx,
    ) -> Self {
        let common_layouts = CommonLayouts::new(data_layout, layouts);
        Self { layouts, data_layout, common_layouts, ir_ctx }
    }

    /// Returns a reference to the [LayoutStore].
    pub fn layouts(&self) -> &LayoutStore {
        self.layouts
    }

    /// Map a function on a particular layout.
    pub fn map_layout<T>(&self, id: LayoutId, func: impl FnOnce(&Layout) -> T) -> T {
        self.layouts.map_fast(id, func)
    }

    /// Get a reference to the data layout of the current
    /// session.
    pub fn data_layout(&self) -> &TargetDataLayout {
        self.data_layout
    }

    /// Returns a reference to the [IrCtx].
    pub fn ir_ctx(&self) -> &IrCtx {
        self.ir_ctx
    }
}

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
    pub fn is_zst(&self, ctx: LayoutCtx) -> bool {
        ctx.layouts().map_fast(self.layout, |layout| match layout.abi {
            AbiRepresentation::Scalar { .. }
            | AbiRepresentation::Pair(..)
            | AbiRepresentation::Vector { .. } => false,
            AbiRepresentation::Aggregate | AbiRepresentation::Uninhabited => {
                layout.size.bytes() == 0
            }
        })
    }

    /// Compute the type of a "field with in a layout" and return the
    /// [LayoutId] associated with the field.
    pub fn field(&self, _ctx: LayoutCtx, _index: usize) -> Self {
        todo!()
    }

    /// Fetch the [Layout] for a variant of the currently
    /// given [Layout].
    pub fn for_variant(&self, ctx: LayoutCtx, variant: VariantIdx) -> Self {
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
                let fields = ctx.ir_ctx().map_on_adt(self.ty, |adt, _| {
                    if adt.variants.is_empty() {
                        panic!("layout::for_variant called on a zero-variant enum")
                    }

                    adt.variant(variant).fields.len()
                });

                // Create a new layout with basically a ZST that is
                // un-inhabited... i.e. `never`
                let shape = if fields == 0 {
                    LayoutShape::Aggregate { offsets: vec![], memory_map: vec![] }
                } else {
                    // @@Todo: this should become a union?
                    todo!()
                };

                ctx.layouts().create(Layout::new(
                    shape,
                    Variants::Single { index: variant },
                    AbiRepresentation::Uninhabited,
                    ctx.data_layout().i8_align,
                    Size::ZERO,
                ))
            }
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

        let alignment_2 = scalar_2.align(ctx);

        // Take the maximum of `scalar_1`, `scalar_2` and the `aggregate` target
        // alignment
        let alignment = scalar_1.align(ctx).max(alignment_2).max(dl.aggregate_align);

        let offset_2 = scalar_1.size(ctx).align_to(alignment.abi);
        let size = (offset_2 + scalar_2.size(ctx)).align_to(alignment.abi);

        Layout {
            shape: LayoutShape::Aggregate {
                offsets: vec![Size::ZERO, offset_2],
                memory_map: vec![0, 1],
            },
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi: AbiRepresentation::Pair(scalar_1, scalar_2),
            alignment,
            size,
        }
    }

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
/// For [`LayoutShape::Struct`], there are two maps stored, the first being all
/// of the field **offset**s in "source" definition order, and a `memory_map`
/// which specifies the actual order of fields in memory in relation to their
/// offsets.
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
        offsets: Vec<Size>,

        /// A map between the specified "source order" of the fields, and
        /// the actual order in memory.
        memory_map: Vec<u32>,
    },
}

impl LayoutShape {
    /// Count the number of fields in the layout shape.
    #[inline]
    pub fn count(&self) -> usize {
        match *self {
            LayoutShape::Primitive => 1,
            LayoutShape::Union { count } => count.get(),
            LayoutShape::Array { elements, .. } => elements.try_into().unwrap(),
            LayoutShape::Aggregate { ref offsets, .. } => offsets.len(),
        }
    }

    /// Get a specific `offset` from the layout shape, and given an
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
            LayoutShape::Aggregate { ref offsets, .. } => offsets[index],
        }
    }

    /// Get the memory index of a specific field in the layout shape, and given
    /// an a "source order" index into the layout. This is used to get the
    /// actual memory order of a field in the layout.
    pub fn memory_index(&self, index: u32) -> u32 {
        match self {
            LayoutShape::Primitive => unreachable!("primitive layout has no defined offsets"),
            LayoutShape::Union { .. } | LayoutShape::Array { .. } => index,
            LayoutShape::Aggregate { memory_map, .. } => memory_map[index as usize],
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
