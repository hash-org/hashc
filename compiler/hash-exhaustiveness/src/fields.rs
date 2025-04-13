//! Data structure that represents the `fields` of a
//! [DeconstructedPat](super::deconstruct::DeconstructedPat). The [Fields] data
//! structure is an inner [Vec] of [DeconstructedPatId]s. It has some useful
//! creation methods for when
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s need to be created
//! from a provided [PatCtx]. [FieldOps] defines methods that operate on
//! [Fields] with the typechecker context available for reading and creating
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s.

use hash_storage::store::statics::StoreId;
use hash_tir::{
    intrinsics::utils::try_use_ty_as_array_ty,
    tir::{CtorDefId, DataDefCtors, DataTy, NodesId, TupleTy, Ty, TyId},
};
use hash_utils::{
    itertools::Itertools,
    thin_vec::{ThinVec, thin_vec},
};

use super::construct::DeconstructedCtor;
use crate::{
    ExhaustivenessChecker, ExhaustivenessEnv, PatCtx,
    storage::{DeconstructedCtorId, DeconstructedPatId},
};

/// Representation of the `fields` that are stored by
/// [DeconstructedPat](super::deconstruct::DeconstructedPat) which are nested
/// patterns.
#[derive(Debug, Clone)]
pub struct Fields {
    /// Vector of the inner ids stored by the [Fields]
    pub fields: ThinVec<DeconstructedPatId>,
}

impl Fields {
    /// Create a [Fields] with no inner elements.
    pub fn empty() -> Self {
        Fields { fields: thin_vec![] }
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

impl<E: ExhaustivenessEnv> ExhaustivenessChecker<'_, E> {
    /// Create [Fields] from an [Iterator] of [Ty]s.
    pub fn wildcards_from_tys(&mut self, tys: impl IntoIterator<Item = TyId>) -> Fields {
        Fields::from_iter(tys.into_iter().map(|ty| {
            let pat = self.wildcard_from_ty(ty);
            self.make_pat(pat)
        }))
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result will have a length of `ctor.arity()`.
    pub(super) fn wildcards_from_ctor(&mut self, ctx: PatCtx, ctor: DeconstructedCtorId) -> Fields {
        let ctor = self.get_ctor(ctor);

        match ctor {
            ctor @ (DeconstructedCtor::Single | DeconstructedCtor::Variant(_)) => {
                match *ctx.ty.value() {
                    Ty::TupleTy(TupleTy { data }) => {
                        let tys =
                            data.elements().borrow().iter().map(|member| member.ty).collect_vec();
                        self.wildcards_from_tys(tys)
                    }
                    Ty::DataTy(DataTy { data_def, .. }) => {
                        // get the variant index from the deconstructed ctor
                        let variant_idx =
                            if let DeconstructedCtor::Variant(idx) = ctor { *idx } else { 0 };

                        // We know that this has to be a non-primitive, so we can immediately get
                        // the variant from the data definition
                        let DataDefCtors::Defined(variants_id) = data_def.borrow().ctors else {
                            panic!("expected a non-primitive data type")
                        };

                        let ctor = CtorDefId::new(variants_id.elements(), variant_idx).borrow();
                        let tys = ctor
                            .params
                            .elements()
                            .borrow()
                            .iter()
                            .map(|member| member.ty)
                            .collect_vec();

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
                let array_ty = try_use_ty_as_array_ty(ctx.ty).unwrap();
                self.wildcards_from_tys((0..arity).map(|_| array_ty.element_ty))
            }
            DeconstructedCtor::Str(..)
            | DeconstructedCtor::IntRange(..)
            | DeconstructedCtor::NonExhaustive
            | DeconstructedCtor::Missing
            | DeconstructedCtor::Wildcard => Fields::empty(),
            DeconstructedCtor::Or => {
                panic!("called `Fields::wildcards` on an `Or` ctor")
            }
        }
    }
}
