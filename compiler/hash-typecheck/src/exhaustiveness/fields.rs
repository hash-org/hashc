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

#[derive(Debug, Clone)]
pub struct Fields {
    pub fields: Vec<DeconstructedPatId>,
}

impl Fields {
    /// Create a [Fields] with no inner elements.
    pub fn empty() -> Self {
        Fields { fields: vec![] }
    }

    /// Returns the list of patterns.
    pub fn iter_patterns(&self) -> impl Iterator<Item = &DeconstructedPatId> {
        self.fields.iter()
    }
}

impl FromIterator<DeconstructedPatId> for Fields {
    fn from_iter<T: IntoIterator<Item = DeconstructedPatId>>(iter: T) -> Self {
        Fields { fields: iter.into_iter().collect() }
    }
}

pub struct FieldOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for FieldOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> FieldOps<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    pub fn wildcards_from_tys(&self, tys: impl IntoIterator<Item = TermId>) -> Fields {
        Fields::from_iter(tys.into_iter().map(|ty| {
            let pat = self.deconstruct_pat_ops().wildcard(ty);
            self.deconstructed_pat_store().create(pat)
        }))
    }

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result must have a length of `ctor.arity()`.
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
                            // @@Remove: when enums aren't represented as this anymore
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
            Constructor::List(_list) => {
                todo!()
                // let arity = list.arity();

                // // Use the oracle to get the inner term `T` for the type...
                // let ty = ...;

                // Fields::wildcards_from_tys((0..arity).map(|_| ty))
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
