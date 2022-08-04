//! Data structure that represents the `fields` of a
//! [DeconstructedPat](super::deconstruct::DeconstructedPat). The [Fields] data
//! structure is an inner [Vec] of [DeconstructedPatId]s. It has some useful
//! creation methods for when
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s need to be created
//! from a provided [PatCtx]. [FieldOps] defines methods that operate on
//! [Fields] with the typechecker context available for reading and creating
//! [DeconstructedPat](super::deconstruct::DeconstructedPat)s.
use itertools::Itertools;

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{
            ConstructorId, DeconstructedPatId, Level1Term, NominalDef, StructFields, Term, TermId,
            TupleTy,
        },
        AccessToStorage, StorageRef,
    },
};

use super::{construct::Constructor, AccessToUsefulnessOps};

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
    pub fn iter_patterns(&self) -> impl Iterator<Item = &DeconstructedPatId> {
        self.fields.iter()
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
    pub(super) fn wildcards(&self, ctx: PatCtx, ctor: ConstructorId) -> Fields {
        let reader = self.reader();
        let ctor = reader.get_ctor(ctor);

        match ctor {
            Constructor::Single | Constructor::Variant(_) => {
                let reader = self.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        let members = reader.get_params(*members);
                        let tys = members.positional().iter().map(|member| member.ty).collect_vec();

                        self.wildcards_from_tys(tys)
                    }
                    Term::Level1(Level1Term::NominalDef(def)) => {
                        match reader.get_nominal_def(*def) {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                StructFields::Explicit(params) => {
                                    let members = reader.get_params(params);
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
            Constructor::List(list) => {
                let arity = list.arity();

                // Use the oracle to get the inner term `T` for the type...
                let Some(ty) = self.oracle().term_as_list(ctx.ty) else {
                        panic!("provided ty is not list as expected: {}", self.for_fmt(ctx.ty))
                };

                self.wildcards_from_tys((0..arity).map(|_| ty))
            }
            Constructor::Str(..)
            | Constructor::IntRange(..)
            | Constructor::NonExhaustive
            | Constructor::Missing { .. }
            | Constructor::Wildcard => Fields::empty(),
            Constructor::Or => {
                panic!("called `Fields::wildcards` on an `Or` ctor")
            }
        }
    }
}
