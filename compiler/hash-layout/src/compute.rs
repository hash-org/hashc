//! Contains all of the logic that computes the layout of an [IrTy].
//! This logic is also designed to avoid doing as much duplicate work
//! as possible, thus using a [LayoutCache] in order to cache all the
//! previously computed layouts, and re-use them as much as possible

use hash_ir::ty::{AdtId, IrTy, IrTyId, RefKind, VariantIdx};
use hash_target::{
    abi::{AbiRepresentation, Integer, Scalar, ScalarKind, ValidScalarRange},
    layout::TargetDataLayout,
    primitives::{FloatTy, SIntTy, UIntTy},
    size::Size,
};
use hash_utils::store::Store;

use crate::{Layout, LayoutCtx, LayoutId, LayoutShape, Variants};

/// This is an auxiliary implementation of computing the
/// layouts of primitive types only, this does not handle ADTs
/// or any more complex types. This function is used to populate
/// [crate::CommonLayouts] table so that it can be used later.
pub(crate) fn compute_primitive_ty_layout(ty: IrTy, dl: &TargetDataLayout) -> Layout {
    let scalar_unit = |value: ScalarKind| {
        let size = value.size(dl);
        Scalar { kind: value, valid_range: ValidScalarRange::full(size) }
    };

    let scalar = |value: ScalarKind| Layout::scalar(dl, scalar_unit(value));

    match ty {
        IrTy::Int(int_ty) => scalar(ScalarKind::from_signed_int_ty(int_ty, dl)),
        IrTy::UInt(uint_ty) => scalar(ScalarKind::from_unsigned_int_ty(uint_ty, dl)),
        IrTy::Float(float_ty) => scalar(float_ty.into()),
        IrTy::Str => {
            // `str` is represented as a scalar pair that contains a
            // pointer to the actual bytes, and then the length of the
            // characters represented as a `usize`.
            let ptr = scalar_unit(ScalarKind::Pointer);
            let len = scalar_unit(ScalarKind::Int { kind: dl.ptr_sized_integer(), signed: false });

            Layout::scalar_pair(dl, ptr, len)
        }
        IrTy::Bool => Layout::scalar(
            dl,
            Scalar {
                kind: ScalarKind::Int { kind: Integer::I8, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 1 },
            },
        ),
        IrTy::Char => Layout::scalar(
            dl,
            Scalar {
                kind: ScalarKind::Int { kind: Integer::I32, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 0x10FFFF },
            },
        ),
        IrTy::Never => Layout {
            shape: LayoutShape::Primitive,
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi: AbiRepresentation::Uninhabited,
            alignment: dl.i8_align,
            size: Size::ZERO,
        },
        _ => unreachable!("encountered non-primitive ty in `compute_primitive_ty_layout`"),
    }
}

impl<'l> LayoutCtx<'l> {
    /// This is the entry point of the layout computation engine. From
    /// here, the [Layout] of a type will be computed all the way recursively
    /// until all of the leaves of the type are also turned into [Layout]s.
    pub fn compute_layout_of_ty(&self, ty: IrTyId) -> LayoutId {
        let dl = self.data_layout;

        let scalar_unit = |value: ScalarKind| {
            let size = value.size(dl);
            Scalar { kind: value, valid_range: ValidScalarRange::full(size) }
        };

        self.ir_ctx.tys().map_fast(ty, |ty| match ty {
            IrTy::Int(ty) => match ty {
                SIntTy::I8 => self.common_layouts.i8,
                SIntTy::I16 => self.common_layouts.i16,
                SIntTy::I32 => self.common_layouts.i32,
                SIntTy::I64 => self.common_layouts.i64,
                SIntTy::I128 => self.common_layouts.i128,
                SIntTy::ISize => self.common_layouts.isize,

                // @@Layout: for bigints, we will probably use a ScalarPair
                // to represent a pointer to the digit array, and then a
                // length of the digits.
                SIntTy::IBig => todo!(),
            },
            IrTy::UInt(ty) => match ty {
                UIntTy::U8 => self.common_layouts.u8,
                UIntTy::U16 => self.common_layouts.u16,
                UIntTy::U32 => self.common_layouts.u32,
                UIntTy::U64 => self.common_layouts.u64,
                UIntTy::U128 => self.common_layouts.u128,
                UIntTy::USize => self.common_layouts.usize,
                UIntTy::UBig => todo!(),
            },
            IrTy::Float(ty) => match ty {
                FloatTy::F32 => self.common_layouts.f32,
                FloatTy::F64 => self.common_layouts.f64,
            },
            IrTy::Str => self.common_layouts.str,
            IrTy::Bool => self.common_layouts.bool,
            IrTy::Char => self.common_layouts.char,
            IrTy::Never => self.common_layouts.never,
            IrTy::Ref(_, _, RefKind::Raw | RefKind::Normal) => {
                let data_ptr = scalar_unit(ScalarKind::Pointer);
                self.layouts().create(Layout::scalar(dl, data_ptr))
            }

            // @@Todo: figure out how to handle rc pointers, probably the same
            // as normal ones, but the underlying type of the pointer may be
            // wrapped in some kind of `Rc` struct?
            IrTy::Ref(_, _, RefKind::Rc) => todo!(),
            IrTy::Slice(_) => todo!(),
            IrTy::Array { ty, size } => self.compute_layout_of_array(*ty, *size as u64),
            IrTy::Adt(adt) => self.compute_layout_of_adt(*adt),
            IrTy::Fn { .. } => todo!(),
        })
    }

    /// Compute the layout of a given [AdtId].
    fn compute_layout_of_adt(&self, _adt: AdtId) -> LayoutId {
        todo!()
    }

    /// Compute the layout of a given [`IrTy::Array`].
    fn compute_layout_of_array(&self, element_ty: IrTyId, element_count: u64) -> LayoutId {
        // first, we compute the layout of the element type

        let element = self.compute_layout_of_ty(element_ty);
        let (element_size, element_alignment) =
            self.layouts().map_fast(element, |element| (element.size, element.alignment));

        // If the size of the array is 0, we can conclude that the
        // abi representation of the array is uninhabited, like a ZST.
        let abi = if element_count == 0 {
            AbiRepresentation::Uninhabited
        } else {
            AbiRepresentation::Aggregate
        };

        // @@LayoutErrors: handle the overflow here as a layout error
        // and then emit an equivalent diagnostic within the compiler.
        let size = element_size.checked_mul(element_count, self.data_layout()).unwrap();

        self.layouts().create(Layout {
            shape: LayoutShape::Array { stride: element_size, elements: element_count },
            abi,
            size,
            alignment: element_alignment,
            variants: Variants::Single { index: VariantIdx::new(0) },
        })
    }
}
