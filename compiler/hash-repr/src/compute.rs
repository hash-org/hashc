//! Contains all of the logic that computes the layout of an [ReprTy].
//! This logic is also designed to avoid doing as much duplicate work
//! as possible, thus using a [LayoutCache] in order to cache all the
//! previously computed layouts, and re-use them as much as possible

use std::{cmp, iter, num::NonZeroUsize};

use derive_more::Constructor;
use hash_storage::store::{
    Store,
    statics::{SingleStoreValue, StoreId},
};
use hash_target::{
    abi::{AbiRepresentation, AddressSpace, Integer, Scalar, ScalarKind, ValidScalarRange},
    alignment::{Alignment, Alignments},
    data_layout::{HasDataLayout, TargetDataLayout},
    primitives::{FloatTy, SIntTy, UIntTy},
    size::Size,
};
use hash_utils::index_vec::IndexVec;

use crate::{
    CommonLayouts, FieldLayout, Layout, LayoutId, LayoutShape, LayoutStorage, LayoutStore,
    PointeeInfo, PointerKind, TyInfo, Variants, repr_stores,
    ty::{Adt, AdtRepresentation, Mutability, RefKind, ReprTy, ReprTyId, VariantIdx},
};

/// This describes the collection of errors that can occur
/// when computing the layout of a type. This is used to
/// report that either a type within a layout cannot be
/// computed because the size is unknown, it is too large, or
/// it is an invalid type.
#[derive(Debug)]
pub enum LayoutError {
    /// Overflow. The computed layout exceeds the maximum object size
    /// specified on the target platform. For more information, see
    /// [`TargetDataLayout::obj_size_bound()`].
    Overflow,

    /// The layout of the type is unknown, this is used
    /// for when the type that is given does not have a well
    /// defined layout.
    Unknown(ReprTyId),
}

/// This is an auxiliary implementation of computing the
/// layouts of primitive types only, this does not handle ADTs
/// or any more complex types. This function is used to populate
/// [crate::CommonLayouts] table so that it can be used later.
pub(crate) fn compute_primitive_ty_layout(ty: ReprTy, dl: &TargetDataLayout) -> Layout {
    let scalar_unit = |value: ScalarKind| {
        let size = value.size(dl);
        Scalar::Initialised { kind: value, valid_range: ValidScalarRange::full(size) }
    };

    let scalar = |value: ScalarKind| Layout::scalar(dl, scalar_unit(value));

    match ty {
        ReprTy::Int(int_ty) => scalar(ScalarKind::from_signed_int_ty(int_ty, dl)),
        ReprTy::UInt(uint_ty) => scalar(ScalarKind::from_unsigned_int_ty(uint_ty, dl)),
        ReprTy::Float(float_ty) => scalar(float_ty.into()),

        // This is represented as an un-sized pointer to the actual data. In ReprTys, the
        // `str` type is always behind a pointer.
        ReprTy::Str => Layout {
            shape: LayoutShape::Array { stride: Size::from_bytes(1), elements: 0 },
            variants: Variants::Single { index: VariantIdx::new(0) },
            abi: AbiRepresentation::Aggregate,
            alignment: dl.i8_align,
            size: Size::ZERO,
        },
        ReprTy::Bool => Layout::scalar(
            dl,
            Scalar::Initialised {
                kind: ScalarKind::Int { kind: Integer::I8, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 1 },
            },
        ),
        ReprTy::Char => Layout::scalar(
            dl,
            Scalar::Initialised {
                kind: ScalarKind::Int { kind: Integer::I32, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 0x10FFFF },
            },
        ),
        ReprTy::Never => Layout {
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

/// A auxiliary context for methods defined on [Layout]
/// which require access to other [Layout]s.
#[derive(Clone, Copy, Constructor)]
pub struct LayoutComputer<'l> {
    /// A reference to the [LayoutStorage].
    ctx: &'l LayoutStorage,
}

impl HasDataLayout for LayoutComputer<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.ctx.data_layout
    }
}

impl LayoutComputer<'_> {
    /// Returns a reference to the [LayoutStorage].
    pub fn ctx(&self) -> &LayoutStorage {
        self.ctx
    }

    /// Returns a reference to the layout store.
    pub fn store(&self) -> &LayoutStore {
        repr_stores().layouts()
    }

    /// Get a reference to the [CommonLayout]s that are available
    /// in the current session.
    pub(crate) fn common_layouts(&self) -> &CommonLayouts {
        &self.ctx.common_layouts
    }

    /// Compute the [Size] of a [ReprTyId].
    pub fn size_of_ty(&self, ty: ReprTyId) -> Result<Size, LayoutError> {
        Ok(self.layout_of_ty(ty)?.size())
    }

    /// This is the entry point of the layout computation engine. From
    /// here, the [Layout] of a type will be computed all the way recursively
    /// until all of the leaves of the type are also turned into [Layout]s.
    pub fn layout_of_ty(&self, ty_id: ReprTyId) -> Result<LayoutId, LayoutError> {
        let dl = self.data_layout();

        let scalar_unit = |value: ScalarKind| {
            let size = value.size(dl);
            Scalar::Initialised { kind: value, valid_range: ValidScalarRange::full(size) }
        };

        // Check if we have already computed the layout of this type.
        if let Some(layout) = self.ctx.cache().get(&ty_id).copied() {
            return Ok(layout);
        }

        let layout = ty_id.map(|ty| match ty {
            ReprTy::Int(ty) => match ty {
                SIntTy::I8 => Ok(self.common_layouts().i8),
                SIntTy::I16 => Ok(self.common_layouts().i16),
                SIntTy::I32 => Ok(self.common_layouts().i32),
                SIntTy::I64 => Ok(self.common_layouts().i64),
                SIntTy::I128 => Ok(self.common_layouts().i128),
                SIntTy::ISize => Ok(self.common_layouts().isize),
            },
            ReprTy::UInt(ty) => match ty {
                UIntTy::U8 => Ok(self.common_layouts().u8),
                UIntTy::U16 => Ok(self.common_layouts().u16),
                UIntTy::U32 => Ok(self.common_layouts().u32),
                UIntTy::U64 => Ok(self.common_layouts().u64),
                UIntTy::U128 => Ok(self.common_layouts().u128),
                UIntTy::USize => Ok(self.common_layouts().usize),
            },
            ReprTy::Float(ty) => Ok(match ty {
                FloatTy::F32 => self.common_layouts().f32,
                FloatTy::F64 => self.common_layouts().f64,
            }),
            ReprTy::Bool => Ok(self.common_layouts().bool),
            ReprTy::Char => Ok(self.common_layouts().char),
            ReprTy::Never => Ok(self.common_layouts().never),
            ReprTy::Ref(pointee, _, kind @ (RefKind::Raw | RefKind::Normal)) => {
                let mut data_ptr = scalar_unit(ScalarKind::Pointer(AddressSpace::DATA));

                // If the reference is raw, then we cannot assume that the pointer
                // is not-null.
                if matches!(kind, RefKind::Raw) {
                    data_ptr.valid_range_mut().start = 1;
                }

                // Compute any metadata if we need to.
                let maybe_metadata = pointee.map(|ty| match ty {
                    ReprTy::Str | ReprTy::Slice(_) => Some(scalar_unit(ScalarKind::Int {
                        kind: dl.ptr_sized_integer(),
                        signed: false,
                    })),
                    _ => None,
                });

                // Create the layout for the reference type.
                let layout = match maybe_metadata {
                    Some(meta) => Layout::scalar_pair(dl, data_ptr, meta),
                    None => Layout::scalar(dl, data_ptr),
                };

                Ok(Layout::create(layout))
            }

            // @@Todo: figure out how to handle rc pointers, probably the same
            // as normal ones, but the underlying type of the pointer may be
            // wrapped in some kind of `Rc` struct?
            ReprTy::Ref(_, _, RefKind::Rc) => Err(LayoutError::Unknown(ty_id)),

            // Slices and strings are treated as "unsized" layouts since they
            // are just pointers to the actual data. In terms of `ReprTy`s `str
            // and `[T]` are always behind a pointer.
            ReprTy::Str => Ok(self.common_layouts().str),
            ReprTy::Slice(ty) => {
                let element = self.layout_of_ty(*ty)?;
                let (size, alignment) = element.map(|element| (element.size, element.alignment));

                Ok(Layout::create(Layout {
                    shape: LayoutShape::Array { stride: size, elements: 0 },
                    variants: Variants::Single { index: VariantIdx::new(0) },
                    abi: AbiRepresentation::Aggregate,
                    alignment,
                    size: Size::ZERO,
                }))
            }
            ReprTy::Array { ty, length: size } => self.compute_layout_of_array(*ty, *size as u64),
            ReprTy::Adt(adt) => adt.map(|adt| -> Result<_, LayoutError> {
                // We have to compute the layouts of all of the variants
                // and all of the fields of the variants
                let field_layout_table = adt
                    .variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|field| self.layout_of_ty(field.ty))
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect::<Result<IndexVec<VariantIdx, _>, _>>()?;

                // This is used to check whether a particular variant of the
                // ADT is uninhabited or all of the fields are zero-sized-types.
                let absent = |layouts: &[LayoutId]| {
                    let mut uninhabited = false;
                    let mut zst = true;

                    for layout in layouts.iter() {
                        layout.map(|layout| {
                            uninhabited |= layout.abi.is_uninhabited();
                            zst &= layout.is_zst();
                        })
                    }

                    uninhabited && zst
                };

                // Now we want to find two present variants within the ADT.
                // We compute this to check whether we can perform some additional optimisations
                // on the layout of the ADT. For instance, if this is an enum, and
                // only has one "non-absent" variant, then we can treat it as a
                // uni-variant enum.
                let (first_present, second_present) = {
                    let mut present_variants =
                        field_layout_table.iter_enumerated().filter_map(|(variant, layouts)| {
                            if absent(layouts) { None } else { Some(variant) }
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
                    None if adt.flags.is_enum() => return Ok(self.common_layouts().never),
                    None => VariantIdx::new(0),
                };

                // If it is a struct, tuple or an enum with a single variant,
                // then we treat it as a uni-variant.
                if adt.flags.is_struct()
                    || adt.flags.is_tuple()

                    // @@Future: if in the future, a specific type can be
                    // specified to the discriminant, and or it is in "C" mode,
                    // then we can't perform this optimisation.
                    || (adt.flags.is_enum() && second_present.is_none())
                {
                    let layout = self
                        .compute_layout_of_univariant(
                            first_present,
                            None,
                            &field_layout_table[first_present],
                            &adt.metadata,
                        )
                        .ok_or(LayoutError::Overflow)?;

                    Ok(Layout::create(layout))
                } else if adt.flags.is_union() {
                    Ok(Layout::create(
                        self.compute_layout_of_union(field_layout_table, adt)
                            .ok_or(LayoutError::Unknown(ty_id))?,
                    ))
                } else {
                    // This must be an enum...
                    let layout = self
                        .compute_layout_of_enum(field_layout_table, adt)
                        .ok_or(LayoutError::Overflow)?;
                    Ok(Layout::create(layout))
                }
            }),

            ReprTy::FnDef { .. } => {
                let layout = self
                    .compute_layout_of_univariant(
                        VariantIdx::new(0),
                        None,
                        &[],
                        &AdtRepresentation::default(),
                    )
                    .ok_or(LayoutError::Overflow)?;

                Ok(Layout::create(layout))
            }
            ReprTy::Fn { .. } => {
                // Create a function pointer and specify that it cannot be null.
                let mut data_ptr = scalar_unit(ScalarKind::Pointer(dl.instruction_address_space));
                data_ptr.valid_range_mut().start = 1;

                Ok(Layout::create(Layout::scalar(dl, data_ptr)))
            }
        })?;

        // We cache the layout of the type that was just created
        self.ctx().add_cache_entry(ty_id, layout);

        Ok(layout)
    }

    /// Compute the layout of a "univariant" type. This is a type which only
    /// has one variant, but potentially many fields. This function takes a
    /// [VariantIdx] as an argument since this function may be used to compute
    /// the layout of a single variant of an enum./// If the [AdtRepresentation]
    /// specifies that the representation should follow the standard "C"
    /// layout, as specified in the following
    /// [C standard](https://web.archive.org/web/20181230041359if_/http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf).
    ///
    /// The algorithm for computing the layout of this type is as follows:
    ///
    /// 1. Compute the layout of all of the fields of the type.
    ///
    /// 2. push all of the ZST-like fields to the start of the struct to avoid
    ///    dealing with them between other fields.
    ///
    /// 3. Sort the remaining fields in order of "effective" alignment of each
    ///    field, essentially the largest fields by size and alignment are
    ///    grouped first, and then descending down.
    ///
    /// 4. try and optimise the ABI of the given type to represent it as a
    ///    scalar which means it can reach more optimisations when code is
    ///    generated for this kind.
    ///
    /// N.B. If layout optimisations are not applicable, then steps 2-3 are not
    /// applied.
    fn compute_layout_of_univariant(
        &self,
        index: VariantIdx,
        tag: Option<(Size, Alignment)>,
        field_layouts: &[LayoutId],
        representation: &AdtRepresentation,
    ) -> Option<Layout> {
        let dl = self.data_layout();

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
            self.store().map_many_fast(field_layouts.iter().copied(), |layouts| {
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

        let mut offsets = vec![FieldLayout::zst(); field_layouts.len()];
        let mut offset = Size::ZERO;

        // If the `tag` is present, we need to add the size and align it
        // at the start of the layout.
        if let Some((tag_size, tag_alignment)) = tag {
            alignment = alignment.max(Alignments::new(tag_alignment));
            offset = tag_size.align_to(tag_alignment);
        }

        let mut abi = AbiRepresentation::Aggregate;

        for &i in &inverse_memory_map {
            field_layouts[i as usize].map(|layout| -> Option<()> {
                // We can mark the overall structure as un-inhabited if
                // we've found a field which is un-inhabited.
                if layout.abi.is_uninhabited() {
                    abi = AbiRepresentation::Uninhabited;
                }

                // Update the offset and alignment of the whole layout based
                // on if the alignment of the field is larger than the current
                // alignment of the layout.
                offset = offset.align_to(layout.alignment.abi);
                offsets[i as usize] = FieldLayout { offset, size: layout.size };

                alignment = alignment.max(layout.alignment);

                // Now increase the offset by the size of the field.
                offset = offset.checked_add(layout.size, dl)?;
                Some(())
            })?;
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

        // If we can, we try to convert the aggregate representation into
        // a scalar representation, either being a direct "scalar" or a
        // "scalar pair".
        if size.bytes() > 0 && abi != AbiRepresentation::Uninhabited {
            self.store().map_many_fast(field_layouts.iter().copied(), |fields| {
                // Ignore all of the ZST fields that are present...
                let mut non_zst_fields = fields.iter().enumerate().filter(|(_, f)| !f.is_zst());

                match (non_zst_fields.next(), non_zst_fields.next(), non_zst_fields.next()) {
                    (Some((i, field)), None, None) => {
                        // If the field covers the whole aggregate, and has a scalar/pair ABI, then
                        // this aggregate inherits the same ABI.
                        if offsets[i].offset.bytes() == 0
                            && alignment.abi == field.alignment.abi
                            && size == field.size
                        {
                            match field.abi {
                                AbiRepresentation::Scalar(_) | AbiRepresentation::Vector { .. }
                                    if optimise_field_order =>
                                {
                                    abi = field.abi;
                                }
                                AbiRepresentation::Pair(..) => {
                                    abi = field.abi;
                                }
                                _ => {}
                            }
                        }
                    }

                    // Two non-ZST fields, and they're both scalars. This is required to represent
                    // items that are considered to be "scalar pair"s and thus
                    // they should have the same ABI representation.
                    (Some((i, a)), Some((j, b)), None) => {
                        if let (AbiRepresentation::Scalar(a), AbiRepresentation::Scalar(b)) =
                            (a.abi, b.abi)
                        {
                            // Resolve the memory order of the fields, not the source
                            // order since they could be re-arranged.
                            let ((i, a), (j, b)) = if offsets[i].offset < offsets[j].offset {
                                ((i, a), (j, b))
                            } else {
                                ((j, b), (i, a))
                            };

                            let pair = Layout::scalar_pair(self.data_layout(), a, b);
                            let pair_offsets = match pair.shape {
                                LayoutShape::Aggregate { ref fields, ref memory_map } => {
                                    debug_assert_eq!(memory_map, &[0, 1]);
                                    fields
                                }
                                _ => unreachable!("scalar pair layout shape is non-aggregate"),
                            };

                            // Now verify that if the scalar pair matches in offsets and size
                            // to the original aggregate, then we can use the scalar pair
                            // representation for the ABI.
                            if offsets[i].offset == pair_offsets[0].offset
                                && offsets[j].offset == pair_offsets[1].offset
                                && pair.size == size
                                && pair.alignment == alignment
                            {
                                abi = pair.abi;
                            }
                        }
                    }

                    // Otherwise, we can't do anything here.
                    _ => {}
                }
            })
        }

        Some(Layout {
            variants: Variants::Single { index },
            shape: LayoutShape::Aggregate { fields: offsets, memory_map },
            abi,
            alignment,
            size,
        })
    }

    /// Compute the layout of a `union` type. Take the layouts of all of the
    /// specified fields, take the maximum size and alignment, and the create
    /// the [Layout].
    ///
    /// N.B. the [Layout] of a union cannot be known if there are no fields
    /// within the union.
    fn compute_layout_of_union(
        &self,
        field_layout_table: IndexVec<VariantIdx, Vec<LayoutId>>,
        data: &Adt,
    ) -> Option<Layout> {
        debug_assert!(data.flags.is_union());

        let mut alignment = self.data_layout().aggregate_align;
        let optimize_union_abi = !data.metadata.inhibits_union_abi_optimisations();

        let mut size = Size::ZERO;
        let mut abi = AbiRepresentation::Aggregate;

        let index = VariantIdx::new(0);

        for field in field_layout_table[index].iter() {
            field.map(|field| {
                alignment = alignment.max(field.alignment);

                // If all non-ZST fields have the same ABI, we can then
                // re-use the ABI for this particular layout.
                if optimize_union_abi && !field.is_zst() {
                    // This discards all of the valid range information and
                    // converts the scalars and allows undefined values.
                    let field_abi = match field.abi {
                        AbiRepresentation::Scalar(scalar) => {
                            AbiRepresentation::Scalar(scalar.to_union())
                        }
                        AbiRepresentation::Pair(first, second) => {
                            AbiRepresentation::Pair(first.to_union(), second.to_union())
                        }
                        AbiRepresentation::Vector { elements, kind } => {
                            AbiRepresentation::Vector { elements, kind: kind.to_union() }
                        }
                        AbiRepresentation::Uninhabited | AbiRepresentation::Aggregate => {
                            AbiRepresentation::Aggregate
                        }
                    };

                    if size == Size::ZERO {
                        abi = field_abi;
                    } else if abi != field_abi {
                        abi = AbiRepresentation::Aggregate;
                    }
                }

                // Take the `max(size, field.size)` since we're looking for the
                // largest field of the union.
                size = size.max(field.size);
            })
        }

        Some(Layout {
            shape: LayoutShape::Union {
                count: NonZeroUsize::new(field_layout_table[index].len())?,
            },
            variants: Variants::Single { index },
            abi,
            alignment,
            size,
        })
    }

    /// Compute the range of values that the discriminants of an [Adt]. This
    /// will compute the minimum and maximum values that the discriminant
    /// can take.
    fn compute_discriminant_range(
        &self,
        adt: &Adt,
        variant_layouts: &IndexVec<VariantIdx, Vec<LayoutId>>,
    ) -> (i128, i128) {
        let (mut min, mut max) = (i128::MAX, i128::MIN);

        let discr_ty = adt.discriminant_ty();
        let bits = discr_ty.size(self.data_layout().pointer_size).bits();

        // Now we iterate through the variants, and compute the range of the
        // discriminant whilst skipping uninhabited variants.
        for (variant, mut value) in adt.discriminants().map(|(v, discr)| (v, discr as i128)) {
            let is_uninhabited =
                self.store().map_many_fast(variant_layouts[variant].iter().copied(), |fields| {
                    fields.iter().any(|f| f.abi.is_uninhabited())
                });

            if is_uninhabited {
                continue;
            }

            // Truncate the value in order so that we avoid over specifying the smallest
            // minimum value in the range, this will effectively clamp the value as always
            // being with the valid `discr_ty` range, which avoid
            // `discriminant_representation()` miscalculating the smallest
            // needed type to actually use for the discriminant in the layout.
            if discr_ty.is_signed() {
                value = (value << (128 - bits)) >> (128 - bits);
            }

            if value < min {
                min = value;
            }

            if value > max {
                max = value;
            }
        }

        // If we had no inhabited variants, we still pretend that there is atleast one
        // variant.
        if min == i128::MAX && max == i128::MIN {
            min = 0;
            max = 0;
        }

        assert!(min <= max, "discriminant range is {min}..{max}");
        (min, max)
    }

    /// Compute the layout of a `enum` type. The algorithm for computing an
    /// `enum` type layout is the following:
    ///
    /// 1. Figure out the type layout of the enum "prefix" tag.
    ///
    /// 2. Compute the layouts of each variant sub-structure, with the applied
    ///    prefix offset.
    ///
    /// 3. Check if the tag can be neatly aligned with the smallest alignment
    ///    from all the variants, which means that the tag is expanded to align
    ///    the type and avoid redundant padding being created when performing
    ///    `load` / `store` operations.
    ///
    /// 4. Attempt to optimise the ABI of the enum by looking at if it can be
    ///    represented as a scalar value.
    ///
    /// 5. Then, collect all of the variant layouts, and build the final layout.
    fn compute_layout_of_enum(
        &self,
        field_layout_table: IndexVec<VariantIdx, Vec<LayoutId>>,
        adt: &Adt,
    ) -> Option<Layout> {
        debug_assert!(adt.flags.is_enum());
        let dl = self.data_layout();
        let mut alignment = dl.aggregate_align;
        let mut size = Size::ZERO;

        // Deal with the alignment of the prefix value
        let (min, max) = self.compute_discriminant_range(adt, &field_layout_table);
        let (prefix_ty, signed) = adt.discriminant_representation(dl, min, max);
        let mut prefix_alignment = prefix_ty.align(dl).abi;

        if adt.metadata.is_c_like() {
            // We need to set the alignment of the prefix to the largest
            // field alignment value.
            for field_row in &field_layout_table {
                for field in field_row {
                    prefix_alignment = prefix_alignment.max(field.borrow().alignment.abi);
                }
            }
        }

        // ##ExpandEnumTagSize
        //
        // Represents the smallest alignment amongst all of the data
        // type variants. Start of from a large alignment value, and
        // work with their way down.
        //
        // This value is used to store the minimum alignment of each
        // field so that we can perform a re-sizing of the enum tag
        // value. On LLVM, we can reduce the amount of un-aligned
        // `load`/`stores` and excessive memcpy/memset operations
        // caused by the un-alignment from the current `prefix_ty`
        // and the alignments of the variants.
        //
        // So, what we do is we take smallest alignment out all of the
        // variants, and try to expand the size of the `prefix_ty` to
        // the alignment size integer.
        //
        // @@BackendDependent(llvm): this "optimisation" might not necessarily
        // apply to other backends than LLVM, so we might not necessarily
        // want to perform this optimisation.
        let mut starting_alignment = Alignment::from_bytes(256).unwrap();

        // Now construct layouts for each variant, and then intern
        // them.
        let mut variant_layouts = field_layout_table
            .iter_enumerated()
            .map(|(index, field_layouts)| {
                // Compute the layout of the starting field, and take the
                // minimum between the existing value, and the variant
                let variant = self.compute_layout_of_univariant(
                    index,
                    Some((prefix_ty.size(), prefix_alignment)),
                    field_layouts,
                    &adt.metadata,
                )?;

                // Compute the layout of the starting field, and take the
                // minimum between the existing value, and the variant
                self.store().map_many_fast(field_layouts.iter().copied(), |fields| {
                    // skip items that are ZSTs or fields with alignment of one
                    // and then compute the min(starting_alignment, field.alignment.abi).
                    for field in
                        variant.shape.iter_increasing_offsets().map(|offset| fields[offset])
                    {
                        if !field.is_zst() || field.alignment.abi.bytes() != 1 {
                            starting_alignment = starting_alignment.min(field.alignment.abi);
                            break;
                        }
                    }
                });

                // update the size and alignment of this value based on the
                // layout and size of the variant.
                size = cmp::max(size, variant.size);
                alignment = alignment.max(variant.alignment);

                Some(variant)
            })
            .collect::<Option<IndexVec<VariantIdx, _>>>()?;

        size = size.align_to(alignment.abi);

        if size.bytes() >= self.data_layout().obj_size_bound() {
            return None;
        }

        // Now that we have computed all of the variants, and figured out the
        // smallest alignment amongst all of the variants, we can now see if
        // we can expand the size of the enum tag value to apply the aforementioned
        // optimisation at ##ExpandEnumTagSize.
        let mut new_prefix_ty = if adt.metadata.is_c_like() || adt.metadata.discriminant.is_some() {
            prefix_ty
        } else {
            // If the alignment is still greater than the maximum integer
            // size, then we will avoid computing thi
            Integer::for_alignment(dl, starting_alignment).unwrap_or(prefix_ty)
        };

        // If the `new_prefix_ty` is larger than the size of the `prefix_ty`,
        // then we perform the re-sizing.

        if new_prefix_ty > prefix_ty {
            let old_prefix_ty_size = prefix_ty.size();
            let new_prefix_ty_size = new_prefix_ty.size();

            for variant in &mut variant_layouts {
                match variant.shape {
                    LayoutShape::Aggregate { fields: ref mut offsets, .. } => {
                        for FieldLayout { offset, .. } in offsets {
                            if *offset <= old_prefix_ty_size {
                                *offset = new_prefix_ty_size;
                            }
                        }
                    }
                    _ => panic!("layout of enum variant is non-aggregate"),
                }

                // If the variant size is smaller or equal to
                // the old size type, we need to expand the struct
                // variant.
                if variant.size <= old_prefix_ty_size {
                    variant.size = new_prefix_ty_size;
                }
            }
        } else {
            new_prefix_ty = prefix_ty;
        }

        // Create the tag value for the enum discriminant
        let tag_mask = new_prefix_ty.size().unsigned_int_max();
        let tag = Scalar::Initialised {
            kind: ScalarKind::Int { kind: new_prefix_ty, signed },
            valid_range: ValidScalarRange {
                start: (min as u128 & tag_mask),
                end: (max as u128 & tag_mask),
            },
        };

        let abi =
            self.compute_enum_abi(&tag, size, alignment, &field_layout_table, &variant_layouts);

        // Now we need to allocate each of the created layouts for the
        // variants.
        let variants =
            variant_layouts.into_iter().map(Layout::create).collect::<IndexVec<VariantIdx, _>>();

        Some(Layout {
            shape: LayoutShape::Aggregate {
                fields: vec![FieldLayout { offset: Size::ZERO, size }],
                memory_map: vec![0],
            },
            variants: Variants::Multiple { tag, field: 0, variants },
            abi,
            alignment,
            size,
        })
    }

    /// Function that computes the ABI of an `enum` like type. This tries
    /// to make the enum be represented as a scalar since this simplifies
    /// code generation (for the enums that can be represented as scalars)
    /// and it can lead from more beneficial optimisations.
    fn compute_enum_abi(
        &self,
        tag: &Scalar,
        enum_size: Size,
        enum_alignment: Alignments,
        field_layouts: &IndexVec<VariantIdx, Vec<LayoutId>>,
        variant_layouts: &IndexVec<VariantIdx, Layout>,
    ) -> AbiRepresentation {
        let dl = self.data_layout();
        let mut abi = AbiRepresentation::Aggregate;

        // If all of the variants are un-inhabited, then this layout
        // is also considered to be un-habited
        if variant_layouts.iter().all(|variant| variant.abi.is_uninhabited()) {
            abi = AbiRepresentation::Uninhabited;
        } else if tag.size(dl) == enum_size {
            // if this enum only contains tags, we represent this enum
            // as a scalar.
            abi = AbiRepresentation::Scalar(*tag);
        } else {
            // If we can represent all of the variant layouts as a scalar,
            // we can then use a scalar-pair representation

            let mut common_prim = None;
            let mut common_prim_initialised_in_all_variants = true;

            for (field_layouts, variant_layout) in field_layouts.iter().zip(variant_layouts) {
                // All variant layouts must be a struct
                let LayoutShape::Aggregate { fields: ref offsets, .. } = variant_layout.shape
                else {
                    panic!("layout of enum variant is non-aggregate");
                };

                let (first, second) =
                    self.store().map_many_fast(field_layouts.iter().copied(), |field_layouts| {
                        let mut fields =
                            iter::zip(field_layouts, offsets).filter(|p| !p.0.is_zst());

                        // @@Hack: ugh we're copying this here because we don't have the accessed
                        // here, maybe we should avoid immediately writing
                        // the fields into the store so we can pass them
                        // down without constantly re-reading them?
                        let first =
                            fields.next().map(|(field, offset)| ((*field).clone(), *offset));
                        let second =
                            fields.next().map(|(field, offset)| ((*field).clone(), *offset));

                        (first, second)
                    });

                let (field, offset) = match (first, second) {
                    (None, None) => {
                        // If there are no fields, then we can assume that this is
                        // un-initialised.
                        common_prim_initialised_in_all_variants = false;
                        continue;
                    }
                    (Some(field), None) => field,
                    _ => {
                        common_prim = None;
                        break;
                    }
                };

                let prim = match field.abi {
                    AbiRepresentation::Scalar(scalar) => {
                        common_prim_initialised_in_all_variants &=
                            matches!(scalar, Scalar::Initialised { .. });
                        scalar.kind()
                    }
                    _ => {
                        common_prim = None;
                        break;
                    }
                };

                // If we found a common primitive type in the previous iteration,
                // then we need to check if it is equal to the current primitive
                // and offset.
                if let Some(pair) = common_prim {
                    if pair != (prim, offset) {
                        common_prim = None;
                        break;
                    }
                } else {
                    common_prim = Some((prim, offset));
                }
            }

            // If we found a common primitive type, then we can use a
            // scalar-pair representation in form of `(tag, prim_scalar)`
            if let Some((prim, offset)) = common_prim {
                let primitive_size = prim.size(dl);
                let primitive_scalar = if common_prim_initialised_in_all_variants {
                    Scalar::Initialised {
                        kind: prim,
                        valid_range: ValidScalarRange::full(primitive_size),
                    }
                } else {
                    Scalar::Union { kind: prim }
                };

                let pair = Layout::scalar_pair(dl, *tag, primitive_scalar);
                let pair_offsets = match pair.shape {
                    LayoutShape::Aggregate { fields: ref offsets, .. } => offsets,
                    _ => panic!("layout of scalar pair is non-aggregate"),
                };

                // If the offsets are equal to the common offset, then we can
                // use this as the ABI representation of the enum.
                if pair_offsets[0].offset == Size::ZERO
                    && pair_offsets[1] == offset
                    && enum_alignment == pair.alignment
                    && enum_size == pair.size
                {
                    abi = pair.abi;
                }
            }
        }

        abi
    }

    /// Compute the layout of a given [`ReprTy::Array`]. This function returns
    /// an optional
    fn compute_layout_of_array(
        &self,
        element_ty: ReprTyId,
        element_count: u64,
    ) -> Result<LayoutId, LayoutError> {
        // first, we compute the layout of the element type

        let element = self.layout_of_ty(element_ty)?;
        let (element_size, element_alignment) =
            element.map(|layout| (layout.size, layout.alignment));

        // If the size of the array is 0, we can conclude that the
        // abi representation of the array is uninhabited, like a ZST.
        let abi = if element_count == 0 {
            AbiRepresentation::Uninhabited
        } else {
            AbiRepresentation::Aggregate
        };

        // Now compute the size by multiplying the element size by the
        // element count. If the multiplication overflows, then we
        // return an error since the array is too big.
        let size = element_size
            .checked_mul(element_count, self.data_layout())
            .ok_or(LayoutError::Overflow)?;

        Ok(Layout::create(Layout {
            shape: LayoutShape::Array { stride: element_size, elements: element_count },
            abi,
            size,
            alignment: element_alignment,
            variants: Variants::Single { index: VariantIdx::new(0) },
        }))
    }

    /// This function computes the layout information of a pointee of a pointer
    /// at a given offset.
    pub fn compute_layout_info_of_pointee_at(
        &self,
        info: TyInfo,
        offset: Size,
    ) -> Option<PointeeInfo> {
        // Check in the cache if we have already computed this information.
        if let Some(pointee_info) = self.ctx().pointee_info_cache.borrow().get(&(info.ty, offset)) {
            return *pointee_info;
        }

        let result = info.ty.map(|ty| match ty {
            ReprTy::Fn { .. } if offset == Size::ZERO => {
                let (size, alignment) =
                    info.layout.map(|layout| (layout.size, layout.alignment.abi));
                Some(PointeeInfo { size, alignment, kind: None })
            }
            ReprTy::Ref(pointee, mutability, ref_kind) if offset.bytes() == 0 => {
                // @@Todo: be more sophisticated with different pointer kinds, and
                // also deal with Rc specifics here..., and potentially disabling
                // this optimisation if we are building in debug mode.
                let kind = match (mutability, ref_kind) {
                    (_, RefKind::Raw) => None,
                    (Mutability::Mutable, _) => Some(PointerKind::Shared),
                    (Mutability::Immutable, _) => Some(PointerKind::Frozen),
                };

                self.layout_of_ty(*pointee).ok().map(|layout| {
                    let (size, alignment) =
                        layout.map(|layout| (layout.size, layout.alignment.abi));
                    PointeeInfo { size, alignment, kind }
                })
            }
            _ => {
                let data_variant = info.layout.map(|layout| {
                    if let LayoutShape::Union { .. } = layout.shape { None } else { Some(info) }
                });

                let mut result = None;

                if let Some(variant) = data_variant {
                    let ptr_end =
                        offset + ScalarKind::Pointer(AddressSpace::DATA).size(self.data_layout());

                    // @@Copying: we can't really do anything about this copy...
                    let shape = variant.layout.borrow().shape.clone();

                    for i in 0..shape.count() {
                        let field_start = shape.offset(i);

                        if field_start <= offset {
                            let field = variant.field(*self, i);
                            let size = field.size();

                            result = if ptr_end <= field_start + size {
                                self.compute_layout_info_of_pointee_at(field, offset - field_start)
                            } else {
                                None
                            };

                            if result.is_some() {
                                break;
                            }
                        }
                    }
                }

                result
            }
        });

        // Cache the result of the computation...
        self.ctx().pointee_info_cache.borrow_mut().insert((info.ty, offset), result);
        result
    }
}
