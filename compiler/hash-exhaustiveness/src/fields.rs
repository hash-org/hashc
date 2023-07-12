//! Data structure that represents the `fields` of a
//! [DeconstructedPat](super::deconstruct::DeconstructedPat). The [Fields] data
//! structure is an inner [Vec] of [DeconstructedPatId]s. It has some useful
//! creation methods for when
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s need to be created
//! from a provided [PatCtx]. [FieldOps] defines methods that operate on
//! [Fields] with the typechecker context available for reading and creating
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s.

use hash_tir::{
    data::{ArrayCtorInfo, DataDefCtors, DataTy, PrimitiveCtorInfo},
    tuples::TupleTy,
    ty_as_variant,
    tys::{Ty, TyId},
    utils::common::CommonUtils,
};
use hash_utils::{itertools::Itertools, store::Store};

use super::construct::DeconstructedCtor;
use crate::{
    storage::{DeconstructedCtorId, DeconstructedPatId},
    ExhaustivenessChecker, PatCtx,
};

/// Representation of the `fields` that are stored by
/// [DeconstructedPat](super::deconstruct::DeconstructedPat) which are nested
/// patterns.
#[derive(Debug, Clone)]
pub struct Fields {
    /// Vector of the inner ids stored by the [Fields]
    pub fields: Vec<DeconstructedPatId>,
}

impl Fields {
    /// Create a [Fields] with no inner elements.
    pub fn empty() -> Self {
        Fields { fields: vec![] }
    }

    /// Returns an [Iterator] of the inner stored [DeconstructedPatId]s.
    pub fn iter_patterns(&self) -> impl Iterator<Item = DeconstructedPatId> + '_ {
        self.fields.iter().copied()
    }

    /// Get the length of the [Fields].
    pub fn len(&self) -> usize {
        self.fields.len()
    }

    /// Check if [Fields] are empty.
    pub fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }
}

impl FromIterator<DeconstructedPatId> for Fields {
    fn from_iter<T: IntoIterator<Item = DeconstructedPatId>>(iter: T) -> Self {
        Fields { fields: iter.into_iter().collect() }
    }
}

impl<'tc> ExhaustivenessChecker<'tc> {
    /// Create [Fields] from an [Iterator] of [Ty]s.
    pub fn wildcards_from_tys(&self, tys: impl IntoIterator<Item = TyId>) -> Fields {
        Fields::from_iter(tys.into_iter().map(|ty| {
            let pat = self.wildcard_from_ty(ty);
            self.deconstructed_pat_store().create(pat)
        }))
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result will have a length of `ctor.arity()`.
    pub(super) fn wildcards_from_ctor(&self, ctx: PatCtx, ctor: DeconstructedCtorId) -> Fields {
        let ctor = self.get_deconstructed_ctor(ctor);

        match ctor {
            ctor @ (DeconstructedCtor::Single | DeconstructedCtor::Variant(_)) => {
                match self.get_ty(ctx.ty) {
                    Ty::Tuple(TupleTy { data }) => {
                        let tys = self.map_params(data, |params| {
                            params.iter().map(|member| member.ty).collect_vec()
                        });

                        self.wildcards_from_tys(tys)
                    }
                    Ty::Data(DataTy { data_def, .. }) => {
                        // get the variant index from the deconstructed ctor
                        let variant_idx =
                            if let DeconstructedCtor::Variant(idx) = ctor { idx } else { 0 };

                        let def = self.get_data_def(data_def);

                        // We know that this has to be a non-primitive, so we can immediately get
                        // the variant from the data definition
                        let DataDefCtors::Defined(variants) = def.ctors else {
                            panic!("expected a non-primitive data type")
                        };

                        let variant = self.get_ctor_def((variants, variant_idx));
                        let tys = self.map_params(variant.params, |params| {
                            params.iter().map(|member| member.ty).collect_vec()
                        });

                        self.wildcards_from_tys(tys)
                    }
                    _ => panic!(
                        "Unexpected ty `{:?}` when getting wildcards in Fields::wildcards",
                        ctx.ty,
                    ),
                }
            }
            DeconstructedCtor::Array(list) => {
                let arity = list.arity();

                let ty = ty_as_variant!(self, self.get_ty(ctx.ty), Data);
                let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(ArrayCtorInfo {
                    element_ty,
                    ..
                })) = self.get_data_def(ty.data_def).ctors
                else {
                    panic!("provided ty is not list as expected: {:?}", ctx.ty)
                };

                self.wildcards_from_tys((0..arity).map(|_| element_ty))
            }
            DeconstructedCtor::Str(..)
            | DeconstructedCtor::IntRange(..)
            | DeconstructedCtor::NonExhaustive
            | DeconstructedCtor::Missing { .. }
            | DeconstructedCtor::Wildcard => Fields::empty(),
            DeconstructedCtor::Or => {
                panic!("called `Fields::wildcards` on an `Or` ctor")
            }
        }
    }
}
