//! Defines all logic regarding computing the layout of types, and
//! representing the said layouts in a way that is usable by the
//! code generation backends.

use hash_ir::{
    ty::{IrTyId, VariantIdx},
    IrCtx,
};
use hash_target::{
    abi::{AbiRepresentation, Scalar},
    alignment::Alignments,
    layout::HasDataLayout,
    size::Size,
};
use hash_utils::{new_store, new_store_key, store::Store};
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
}

impl<'abi> LayoutCtx<'abi> {
    /// Create a new [LayoutCtx].
    pub fn new(layouts: &'abi LayoutStore, ir_ctx: &'abi IrCtx) -> Self {
        Self { layouts, ir_ctx }
    }

    /// Returns a reference to the [LayoutStore].
    pub fn layouts(&self) -> &LayoutStore {
        self.layouts
    }

    /// Map a function on a particular layout.
    pub fn map_layout<T>(&self, id: LayoutId, func: impl FnOnce(&Layout) -> T) -> T {
        self.layouts.map_fast(id, func)
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
    pub fn is_zst(&self, store: &LayoutStore) -> bool {
        store.map_fast(self.layout, |layout| match layout.abi {
            AbiRepresentation::Scalar { .. }
            | AbiRepresentation::Pair(..)
            | AbiRepresentation::Vector { .. } => false,
            AbiRepresentation::Aggregate | AbiRepresentation::Uninhabited => {
                layout.size.bytes() == 0
            }
        })
    }
}

impl TyInfo {
    /// Compute the type of a "field with in a layout" and return the
    /// [LayoutId] associated with the field.
    pub fn field(&self, _ctx: LayoutCtx, _index: usize) -> Self {
        todo!()
    }
}

/// Represents the [Layout] of a particular type in Hash. This captures
/// all possible kinds of type, including primitives, structs, enums, etc.
///
/// The [Layout] contains a `shape` which stores fields that are shared
/// across all *variants* (if the type has multiple variants), and a
/// [Variants] enum which stores information about the variants of the type.
#[derive(Debug)]

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
    pub fn scalar<C: HasDataLayout>(ctx: &C, scalar: Scalar, abi: AbiRepresentation) -> Self {
        let size = scalar.size(ctx);
        let alignment = scalar.align(ctx);

        Self {
            shape: LayoutShape::Primitive,
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi,
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
#[derive(Clone, Debug)]
pub enum LayoutShape {
    /// Primitives, `!` and other scalar-like types have only one specific
    /// layout.
    Primitive,

    /// Layout for array/vector like types that have a known element
    /// count at compile time.
    Array {
        /// The size of each element in the array layout.
        stride: Size,

        /// The number of elements in the array layout.
        elements: u64,
    },

    /// Layout for struct-like types.
    ///
    /// Fields of the `struct`-like type are guaranteed to never overlap, and
    /// gaps between fields are either padding between a field, or space left
    /// over to denote a **discriminant** alignment (in the case of `enum`s).
    Struct {
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
            LayoutShape::Array { elements, .. } => elements.try_into().unwrap(),
            LayoutShape::Struct { ref offsets, .. } => offsets.len(),
        }
    }

    /// Get a specific `offset` from the layout shape, and given an
    /// index into the layout.
    #[inline]
    pub fn offset(&self, index: usize) -> Size {
        match *self {
            LayoutShape::Primitive => unreachable!("primitive layout has no defined offsets"),
            LayoutShape::Array { stride, elements } => {
                let index = index as u64;
                assert!(index < elements);
                stride * index
            }
            LayoutShape::Struct { ref offsets, .. } => offsets[index],
        }
    }

    /// Get the memory index of a specific field in the layout shape, and given
    /// an a "source order" index into the layout. This is used to get the
    /// actual memory order of a field in the layout.
    pub fn memory_index(&self, index: u32) -> u32 {
        match self {
            LayoutShape::Primitive => unreachable!("primitive layout has no defined offsets"),
            LayoutShape::Array { .. } => index,
            LayoutShape::Struct { memory_map, .. } => memory_map[index as usize],
        }
    }

    /// Iterate over offsets in the [LayoutShape] by increasing offsets.
    pub fn iter_increasing_offsets(&self) -> impl Iterator<Item = usize> + '_ {
        let mut inverse = vec![0; self.count()];

        // iterate over the memory map and create the inverse map
        // for the fields in the layout.
        if let LayoutShape::Struct { memory_map, .. } = self {
            for (i, &index) in memory_map.iter().enumerate() {
                inverse[index as usize] = i;
            }
        }

        (0..self.count()).map(move |i| match *self {
            LayoutShape::Primitive | LayoutShape::Array { .. } => i,
            LayoutShape::Struct { .. } => inverse[i],
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
