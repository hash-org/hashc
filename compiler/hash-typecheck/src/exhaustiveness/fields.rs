//! Data structure that represents the `fields` of a
//! [DeconstructedPat](super::deconstruct::DeconstructedPat). The [Fields] data
//! structure is an inner [Vec] of [DeconstructedPatId]s. It has some useful
//! creation methods for when
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s need to be created
//! from a provided [PatCtx]. [FieldOps] defines methods that operate on
//! [Fields] with the typechecker context available for reading and creating
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s.
use hash_types::{terms::TermId, Level1Term, NominalDef, StructFields, Term, TupleTy};
use hash_utils::store::Store;
use itertools::Itertools;

use super::{construct::DeconstructedCtor, AccessToUsefulnessOps};
use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        exhaustiveness::{DeconstructedCtorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
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

pub struct FieldOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for FieldOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> FieldOps<'tc> {
    /// Create a new [FieldOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Create [Fields] from an [Iterator] of [Term]s.
    pub fn wildcards_from_tys(&self, tys: impl IntoIterator<Item = TermId>) -> Fields {
        Fields::from_iter(tys.into_iter().map(|ty| {
            let pat = self.deconstruct_pat_ops().wildcard(ty);
            self.deconstructed_pat_store().create(pat)
        }))
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result will have a length of `ctor.arity()`.
    pub(super) fn wildcards(&self, ctx: PatCtx, ctor: DeconstructedCtorId) -> Fields {
        let reader = self.reader();
        let ctor = reader.get_deconstructed_ctor(ctor);

        match ctor {
            DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                let reader = self.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        let members = reader.get_params_owned(members);
                        let tys = members.positional().iter().map(|member| member.ty).collect_vec();

                        self.wildcards_from_tys(tys)
                    }
                    Term::Level1(Level1Term::NominalDef(def)) => {
                        match reader.get_nominal_def(def) {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                StructFields::Explicit(params) => {
                                    let members = reader.get_params_owned(params);
                                    let tys = members
                                        .positional()
                                        .iter()
                                        .map(|member| member.ty)
                                        .collect_vec();

                                    self.wildcards_from_tys(tys)
                                }
                                StructFields::Opaque => tc_panic!(
                                    ctx.ty,
                                    self,
                                    "Unexpected ty `{}` when getting wildcards in Fields::wildcards",
                                    self.for_fmt(ctx.ty),
                                ),
                            },
                            NominalDef::Unit(_) => {
                                Fields::empty()
                            },
                            // @@EnumToUnion: when enums aren't represented as this anymore
                            NominalDef::Enum(_) => unreachable!(),
                        }
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        self,
                        "Unexpected ty `{}` when getting wildcards in Fields::wildcards",
                        self.for_fmt(ctx.ty),
                    ),
                }
            }
            DeconstructedCtor::List(list) => {
                let arity = list.arity();

                // Use the oracle to get the inner term `T` for the type...
                let Some(ty) = self.oracle().term_as_list_ty(ctx.ty) else {
                        panic!("provided ty is not list as expected: {}", self.for_fmt(ctx.ty))
                };

                self.wildcards_from_tys((0..arity).map(|_| ty))
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
