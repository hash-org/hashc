use std::ops::Deref;

use hash_repr::{
    TyInfo, Variants,
    compute::LayoutComputer,
    constant::{Const, ConstKind},
    ty::{ReprTy, ToReprTy, VariantIdx},
};
use hash_source::constant::AllocRange;
use hash_storage::store::statics::StoreId;
use hash_target::size::Size;
use hash_utils::{derive_more::Constructor, itertools::Itertools};

/// Utility structure used to represent what a [Const] is destructured into
/// by [`ConstUtils::destructure_const`]. This is useful for when the [Const]
/// needs to be inspected field-by-field.
#[derive(Clone, Debug)]
pub struct DestructuredConst {
    /// The variant index of the [Const] if it is an enum. This is `None` if
    /// the [Const] is not an ADT, i.e. an array.
    pub variant: Option<VariantIdx>,

    /// The newly generated top-level [Const]s that the original [Const] was
    /// deconstructed into. Each of these [Const]s could again be destrcutured
    /// into further fields.
    pub fields: Vec<Const>,
}

/// Utilties for reading [Const] data and performing various other
/// operations on the [Const] representation.
#[derive(Constructor)]
pub struct ConstUtils<'ctx> {
    /// The [LayoutComputer] is used to compute the layout of the data
    /// under the constant.
    lc: LayoutComputer<'ctx>,

    /// The constant that is being operated on.
    inner: &'ctx Const,
}

impl Deref for ConstUtils<'_> {
    type Target = Const;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl ConstUtils<'_> {
    /// Compute a [TyInfo] from a [Const].
    pub(crate) fn ty_info(&self) -> TyInfo {
        let ty = self.ty();
        TyInfo { ty, layout: self.lc.layout_of_ty(ty).unwrap() }
    }

    /// Create a inner [Const] (a field) from a field, and the [AllocId]
    /// that backs the current constant.
    fn field_from_alloc(&self, offset: Size, field_info: TyInfo) -> Const {
        // @@Correctness: should we really return a `Zero` here?
        if field_info.layout.is_zst() {
            return Const::new(field_info.ty, ConstKind::Zero);
        }

        // Check if we can just use a scalar value here..
        let try_as_scalar = match field_info.ty.value() {
            ty if ty.is_scalar() => true,
            ReprTy::Ref(ty, _, _) => {
                ty.map(|inner| matches!(inner, ReprTy::Str | ReprTy::Slice(_)))
            }
            _ => false,
        };

        let alloc = self.as_alloc();

        if try_as_scalar {
            let range = AllocRange::new(offset, field_info.layout.size());
            let scalar = alloc.borrow().read_scalar(range, &self.lc);
            Const::new(field_info.ty, ConstKind::Scalar(scalar))
        } else {
            // We essentially move the offset to the field, and update the
            // type so that the inner readers can perform the same operation
            // until we reach a leaf `ConstKind`, i.e. a zero or a scalar.
            Const::new(field_info.ty, ConstKind::Alloc { offset, alloc })
        }
    }

    /// Read the discriminant of the given [Const]. If the [Const] is not an
    /// allocation then this will return `None`. This will return the
    /// [VariantIdx] and the relative offset of the data that is stored in
    /// the allocation.
    fn read_discriminant(&self) -> Option<(Size, VariantIdx)> {
        let info = self.ty_info();
        let ConstKind::Alloc { offset, alloc } = self.kind() else { return None };

        // Read the layout variant and deduce either the variant-idx, or
        // the tag to later compute the tag.
        let (tag, field) = match info.layout.borrow().variants {
            // @@FixMe: `Single` is still used to represent the layout for an `enum`
            // which has no variatns. Perhaps this should return `0` on it?
            Variants::Single { index } => return Some((offset, index)),
            Variants::Multiple { tag, field, .. } => (tag, field),
        };

        // We have to look more precisely at the layout to determine
        // the actual 'variant' index.
        let tag_layout = self.lc.layout_of_ty(tag.kind().int_ty().to_repr_ty()).ok()?;
        let tag_size = tag_layout.size();

        // We need to read the value at the given field offset.
        let offset = offset + info.layout.offset_of(field);
        let range = AllocRange::new(offset, tag_size);
        let data = alloc.borrow().read_scalar(range, &self.lc).assert_bits(tag_size);

        let (variant, _) = match info.ty.value() {
            ReprTy::Adt(def) => def
                .borrow()
                .discriminants()
                .find(|(_, val)| *val == data)
                .unwrap_or_else(|| panic!("couldn't find computed discriminant in type")),
            _ => unreachable!(),
        };

        Some((offset, variant))
    }

    /// Destructure the [Const] into the given children fields. This is useful
    /// for when the [Const] needs to be inspected field-by-field.
    ///
    /// ##Note: This only destructures the top-level fields of the constant. It
    /// is intended that this is recursively called on each further field to
    /// then destructure that field.
    pub fn destructure_const(&self) -> Option<DestructuredConst> {
        let info @ TyInfo { ty, layout } = self.ty_info();
        let value @ ConstKind::Alloc { mut offset, .. } = self.kind() else { return None };

        let (variant, field_count, downcasted_layout) = match ty.value() {
            ReprTy::Array { length, .. } => (None, length, layout),
            ReprTy::Adt(def) if def.borrow().variants.is_empty() => return None,
            ReprTy::Adt(def) => {
                let (offset_with_tag, variant) = self.read_discriminant()?;
                let variant_layout = info.for_variant(self.lc, variant);
                offset = offset_with_tag;

                (Some(variant), def.borrow().variant(variant).fields.len(), variant_layout.layout)
            }
            ty => panic!("cannot destructure a non-aggregate value: {value:?} ty: {ty:?}"),
        };

        // ##Note: we're using the same `ty` here even for the case
        // where the enum variant is downcasted. This is fine since the
        // layout representation is intended to work for this case. We
        // will still have to call `field()` with the enum type, but the
        // specific layout of the variant that we care about... which we
        // just computed.
        let downcasted_info = TyInfo::new(ty, downcasted_layout);

        // Now we can actually destructure the value into the fields.
        let fields = (0..field_count)
            .map(|i| {
                // We essentially have to make a new constant based on the type.
                let field = downcasted_info.field(self.lc, i);
                self.field_from_alloc(offset, field)
            })
            .collect_vec();

        Some(DestructuredConst { variant, fields })
    }

    /// Evaluate the value of the [Scalar] constant into a `u128` value.
    pub fn eval_bits(&self) -> u128 {
        let size = self.lc.size_of_ty(self.ty()).unwrap();

        match self.kind {
            ConstKind::Scalar(scalar) => scalar.to_bits(size).unwrap(),
            _ => panic!("cannot evaluate non-scalar constant"),
        }
    }
}
