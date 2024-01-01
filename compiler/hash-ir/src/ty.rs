//! Simplified Hash type hierarchy. The [ReprTy] is used a simplified
//! variant of the available Hash [Term]s that are defined in the
//! `hash-tir` crate. This data structure is used to remove unnecessary
//! complexity from types that are required for IR generation and
//! analysis.

use hash_ast::ast;
use hash_attrs::{
    attr::{attr_store, Attr, ReprAttr},
    builtin::attrs,
    ty::AttrId,
};
// Re-export everything from `hash-layout` types:
pub use hash_layout::ty::*;
use hash_storage::store::statics::{SingleStoreValue, StoreId};

use crate::ir::{BodyInfo, Place, PlaceProjection};

pub trait InstanceHelpers {
    /// Check if the instance has the specified attribute.
    fn has_attr(&self, attr: impl Into<AttrId>) -> bool;
}

impl InstanceHelpers for Instance {
    fn has_attr(&self, attr: impl Into<AttrId>) -> bool {
        let attr = attr.into();
        attr_store().node_has_attr(self.attr_id, attr)
    }
}

pub trait AdtHelpers {
    /// Apply a given origin onto the ADT. This will update
    /// any representation flags, or anything that can be
    /// derived from attributes that were specified on the ADT.
    fn apply_origin(&mut self, origin: ast::AstNodeId);
}

impl AdtHelpers for Adt {
    fn apply_origin(&mut self, origin: ast::AstNodeId) {
        self.origin = Some(origin);

        attr_store().map_with_default(origin, |attrs| {
            // If we have a representation hint, we update the repr flags
            // on this ADT accordingly...
            if let Some(repr_hint) = attrs.get_attr(attrs::REPR) {
                self.metadata = adt_representation_from_attr(repr_hint);
            }
        })
    }
}

/// Parse a [AdtRepresentation] from an [Attr].
fn adt_representation_from_attr(attr: &Attr) -> AdtRepresentation {
    debug_assert!(attr.id == attrs::REPR);

    let parsed = ReprAttr::parse(attr).unwrap();
    let mut representation = AdtRepresentation::default();

    match parsed {
        ReprAttr::C => {
            representation.add_flags(RepresentationFlags::C_LIKE);
        }
        ReprAttr::Int(value) => {
            debug_assert!(!value.is_big()); // Discriminant cannot be a big int.
            representation.discriminant = Some(value);
        }
    }

    representation
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

impl PlaceTy {
    /// Create a [PlaceTy] from a base [ReprTy]. This is useful for when
    /// you want to apply a single projection on the current type
    /// and create a new [PlaceTy] from the projection.
    pub fn from_ty(ty: ReprTyId) -> Self {
        Self { ty, index: None }
    }

    /// Apply a projection to the current [PlaceTy].
    fn apply_projection(self, projection: PlaceProjection) -> Self {
        match projection {
            PlaceProjection::Downcast(index) => PlaceTy { ty: self.ty, index: Some(index) },
            PlaceProjection::Field(index) => {
                let ty = self
                    .ty
                    .borrow()
                    .on_field_access(index, self.index)
                    .unwrap_or_else(|| panic!("expected an ADT, got {self:?}"));

                PlaceTy { ty, index: None }
            }
            PlaceProjection::Deref => {
                let ty = self
                    .ty
                    .borrow()
                    .on_deref()
                    .unwrap_or_else(|| panic!("expected a reference, got {self:?}"));

                PlaceTy { ty, index: None }
            }
            PlaceProjection::Index(_) | PlaceProjection::ConstantIndex { .. } => {
                let ty = self
                    .ty
                    .map(|ty| ty.on_index())
                    .unwrap_or_else(|| panic!("expected an array or slice, got `{:?}`", self.ty));

                PlaceTy { ty, index: None }
            }
            PlaceProjection::SubSlice { from, to, from_end } => {
                let ty = self.ty.map(|base| match base {
                    ReprTy::Slice(_) => self.ty,
                    ReprTy::Array { ty, .. } if !from_end => {
                        ReprTy::create(ReprTy::Array { ty: *ty, length: to - from })
                    }
                    ReprTy::Array { ty, length: size } if from_end => {
                        ReprTy::create(ReprTy::Array { ty: *ty, length: size - from - to })
                    }
                    _ => panic!("expected an array or slice, got {self:?}"),
                });

                PlaceTy { ty, index: None }
            }
        }
    }

    /// Apply a projection on [PlaceTy] and convert it into
    /// the underlying type.
    pub fn projection_ty(self, projection: PlaceProjection) -> ReprTyId {
        let projected_place = self.apply_projection(projection);
        projected_place.ty
    }

    /// Create a [PlaceTy] from a [Place].
    pub fn from_place(place: Place, info: &BodyInfo) -> Self {
        // get the type of the local from the body.
        let mut base = PlaceTy { ty: info.locals[place.local].ty, index: None };

        for projection in info.projections.borrow(place.projections).iter() {
            base = base.apply_projection(*projection);
        }

        base
    }
}
