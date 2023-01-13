//! Contains all of the logic that computes the layout of an [IrTy].
//! This logic is also designed to avoid doing as much duplicate work
//! as possible, thus using a [LayoutCache] in order to cache all the
//! previously computed layouts, and re-use them as much as possible

use std::cmp;

use hash_ir::ty::{AdtData, AdtId, AdtRepresentation, IrTy, IrTyId, RefKind, VariantIdx};
use hash_target::{
    abi::{AbiRepresentation, Integer, Scalar, ScalarKind, ValidScalarRange},
    alignment::{Alignment, Alignments},
    layout::TargetDataLayout,
    primitives::{FloatTy, SIntTy, UIntTy},
    size::Size,
};
use hash_utils::store::Store;
use index_vec::IndexVec;

use crate::{Layout, LayoutCtx, LayoutId, LayoutShape, Variants};

/// This describes the collection of errors that can occur
/// when computing the layout of a type. This is used to
/// report that either a type within a layout cannot be
/// computed because the size is unknown, it is too large, or
/// it is an invalid type.
pub(crate) enum LayoutError {}

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

/// This function is used to invert a provided memory mapping. The
/// mapping is a [`Vec<u32>`] which is used to map the source field
/// order to the memory order. The values that are stored within the
/// mapping are indices in the source order. This function inverts the
/// mapping so that the values become the memory order, and the indices
/// become the source order.
fn invert_memory_mapping(mapping: &[u32]) -> Vec<u32> {
    let mut result = vec![0; mapping.len()];
    for i in 0..mapping.len() {
        result[mapping[i] as usize] = i as u32;
    }

    result
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
            IrTy::Adt(adt) => self.ir_ctx.map_adt(*adt, |id, adt| {
                // We have to compute the layouts of all of the variants
                // and all of the fields of the variants
                let child_layouts = adt
                    .variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|field| self.compute_layout_of_ty(field.ty))
                            .collect::<Vec<_>>()
                    })
                    .collect::<IndexVec<VariantIdx, _>>();

                // This is used to check whether a particular variant of the
                // ADT is uninhabited or all of the fields are zero-sized-types.
                let absent = |layouts: &[LayoutId]| {
                    let (uninhabited, zst) =
                        self.layouts.map_many_fast(layouts.iter().copied(), |layouts| {
                            (
                                layouts.iter().any(|layout| layout.abi.is_uninhabited()),
                                layouts.iter().all(|layout| layout.is_zst()),
                            )
                        });

                    uninhabited && zst
                };

                // Now we want to find two present variants within the ADT.
                // We compute this to check whether we can perform some additional optimisations
                // on the layout of the ADT. For instance, if this is an enum, and
                // only has one "non-absent" variant, then we can treat it as a
                // uni-variant enum.
                let (first_present, second_present) = {
                    let mut present_variants =
                        child_layouts.iter_enumerated().filter_map(|(variant, layouts)| {
                            if absent(&layouts) {
                                None
                            } else {
                                Some(variant)
                            }
                        });

                    (present_variants.next(), present_variants.next())
                };

                // We perform a transformation on the "first_present" in order
                // to ensure that there is always a `first_present` value even
                // if all of the variants are non-present.
                let first_present = match first_present {
                    Some(variant) => variant,
                    // In the case of where an enum has no inhabited variants,
                    // we return early and return the "never" layout.
                    None if adt.flags.is_enum() => return self.common_layouts.never,
                    None => VariantIdx::new(0),
                };

                // If it is a struct, tuple or an enum with a single variant,
                // then we treat it as a uni-variant.
                if adt.flags.is_struct()
                    || adt.flags.is_tuple()

                    // @@Note: if in the future, a specific type can be 
                    // specified to the discriminant, and or it is in "C" mode,
                    // then we can't perform this optimisation.
                    || (adt.flags.is_enum() && second_present.is_none())
                {
                    self.layouts().create(self.compute_layout_of_univariant(
                        first_present,
                        None,
                        &child_layouts[first_present],
                        &adt.representation,
                    ))
                } else if adt.flags.is_union() {
                    self.compute_layout_of_union(id, adt)
                } else {
                    // This must be an enum...
                    self.compute_layout_of_enum(id, adt)
                }
            }),
            IrTy::Fn { .. } => todo!(),
        })
    }

    /// Compute the layout of a "univariant" type. This is a type which only
    /// has one variant, but potentially many fields. This function takes a
    /// [VariantIdx] as an argument since this function may be used to compute
    /// the layout of a single variant of an enum.
    ///
    /// The algorithm for computing the layout of this type is as follows:
    ///
    /// 1. Compute the layout of all of the fields of the type.
    ///
    /// If the [AdtRepresentation] does not specify any kind of options that
    /// may prevent layout optimisation, then the following algorithm is used:
    ///
    ///
    /// If the [AdtRepresentation] specifies that the representation should
    /// follow the standard "C" layout, as specified in the following
    /// [C standard](https://web.archive.org/web/20181230041359if_/http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf).
    fn compute_layout_of_univariant(
        &self,
        index: VariantIdx,
        tag: Option<(Size, Alignment)>,
        field_layouts: &[LayoutId],
        representation: &AdtRepresentation,
    ) -> Layout {
        let dl = self.data_layout;
        let mut abi = AbiRepresentation::Aggregate;

        let mut alignment = dl.aggregate_align;
        let mut inverse_memory_map: Vec<u32> = (0..field_layouts.len() as u32).collect();

        // If we can perform a re-ordering of the fields based on
        // the representation, then we do it here.
        let optimise_field_order = !representation.inhibits_struct_field_reordering();

        if optimise_field_order {
            // This computes the "effective alignment" of a field. This is basically
            // computed `log2(effective - alignment)` of the field.
            let effective_field_alignment = |layout: &Layout| {
                layout.alignment.abi.bytes().max(layout.size.bytes()).trailing_zeros()
            };

            // We sort the keys by the effective alignment of the field.
            self.layouts().map_many_fast(field_layouts.iter().copied(), |layouts| {
                if tag.is_some() {
                    // Sort the fields in ascending alignment order so that
                    // the layout stays optimal regardless of the prefix.
                    inverse_memory_map.sort_by_key(|&pos| {
                        let field = layouts[pos as usize];
                        effective_field_alignment(field)
                    });
                } else {
                    // push all of the ZSTs to the avoid having strange
                    // offsets later..
                    inverse_memory_map.sort_by_key(|&pos| {
                        let field = layouts[pos as usize];
                        (!field.is_zst(), cmp::Reverse(effective_field_alignment(field)))
                    })
                }
            })
        }

        let mut offsets = vec![Size::ZERO; field_layouts.len()];
        let mut offset = Size::ZERO;

        // If the `tag` is present, we need to add the size and align it
        // at the start of the layout.
        if let Some((tag_size, tag_alignment)) = tag {
            alignment = alignment.max(Alignments::new(tag_alignment));
            offset = tag_size.align_to(tag_alignment);
        }

        for &i in &inverse_memory_map {
            self.layouts().map_fast(field_layouts[i as usize], |layout| {
                let field_alignment = layout.alignment;

                // We can mark the overall structure as un-inhabited if
                // we've found a field which is un-inhabited.
                if layout.abi.is_uninhabited() {
                    abi = AbiRepresentation::Uninhabited;
                }

                // Update the offset and alignment of the whole layout based
                // on if the alignment of the field is larger than the current
                // alignment of the layout.
                offset = offset.align_to(field_alignment.abi);
                offsets[i as usize] = offset;

                alignment = alignment.max(field_alignment);

                // Now increase the offset by the size of the field.
                offset = offset.checked_add(layout.size, dl).unwrap();
            })
        }

        // Now we can compute the size of the layout, we take the last
        // computed "offset" and then align it to the specified ABI
        // alignment.
        let size = offset.align_to(alignment.abi);
        let memory_map = if optimise_field_order {
            invert_memory_mapping(&inverse_memory_map)
        } else {
            inverse_memory_map
        };

        Layout {
            variants: Variants::Single { index },
            shape: LayoutShape::Struct { offsets, memory_map },
            abi,
            alignment,
            size,
        }
    }

    /// Compute the layout of a `union` type.
    fn compute_layout_of_union(&self, _id: AdtId, data: &AdtData) -> LayoutId {
        debug_assert!(data.flags.is_union());

        todo!()
    }

    /// Compute the layout of a `enum` type.
    fn compute_layout_of_enum(&self, _id: AdtId, data: &AdtData) -> LayoutId {
        debug_assert!(data.flags.is_enum());

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
