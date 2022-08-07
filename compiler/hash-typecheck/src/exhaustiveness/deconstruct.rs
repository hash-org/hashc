//! This file contains logic surrounding [DeconstructedPat] which is a
//! representation of a [Pat] that is deconstructed and simplified
//! to the point of being processable by the usefulness algorithm. A
//! [DeconstructedPat] is essentially a tree representation of a
//! [Pat] with any of the inner fields of the [Pat] being represented
//! as child [DeconstructedPat]s stored within the `fields` parameter
//! of the structure.
use std::{cell::Cell, fmt::Debug};

use hash_utils::store::Store;
use itertools::Itertools;
use smallvec::SmallVec;

use super::{construct::DeconstructedCtor, fields::Fields, AccessToUsefulnessOps};
use crate::{
    exhaustiveness::{list::ListKind, PatCtx},
    fmt::{ForFormatting, PrepareForFormatting},
    ops::AccessToOps,
    storage::{
        deconstructed::{DeconstructedCtorId, DeconstructedPatId},
        pats::PatId,
        primitives::{Level1Term, NominalDef, Term},
        terms::TermId,
        AccessToStorage, StorageRef,
    },
};

/// A [DeconstructedPat] is a representation of a [DeconstructedCtor] that is
/// split between the constructor subject `ctor` and the `fields` that the
/// constructor holds.
#[derive(Debug, Clone)]
pub struct DeconstructedPat {
    /// The subject of the [DeconstructedPat].
    pub ctor: DeconstructedCtorId,
    /// Any fields that are applying to the subject of the
    /// [DeconstructedPat]
    pub fields: Fields,
    /// The type of the current deconstructed pattern
    pub ty: TermId,
    /// An associated [crate::storage::primitives::Pat] that can be used
    /// for reporting reachability and printing of patterns.
    pub id: Option<PatId>,
    /// Whether the current pattern is reachable.
    pub reachable: Cell<bool>,
    /// Whether the current deconstructed pat has a guard, it's usually false
    /// so all the functions that construct this type assume that it is false
    pub has_guard: Cell<bool>,
}

impl DeconstructedPat {
    /// Create a new [DeconstructedPat]
    pub(super) fn new(
        ctor: DeconstructedCtorId,
        fields: Fields,
        ty: TermId,
        id: Option<PatId>,
    ) -> Self {
        DeconstructedPat {
            ctor,
            fields,
            id,
            ty,
            reachable: Cell::new(false),
            has_guard: Cell::new(false),
        }
    }

    /// We keep track for each pattern if it was ever reachable during the
    /// analysis. This is used with `unreachable_spans` to report
    /// unreachable sub-patterns arising from or patterns.
    pub(super) fn set_reachable(&self) {
        self.reachable.set(true)
    }
    pub(super) fn is_reachable(&self) -> bool {
        self.reachable.get()
    }
}

pub struct DeconstructPatOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for DeconstructPatOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> DeconstructPatOps<'tc> {
    /// Create a new [DeconstructPatOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Create a `match-all` [DeconstructedPat] and infer [Fields] as
    /// from the provided type in the context, this is only to be used
    /// when creating `match-all` wildcard patterns.
    pub(super) fn wild_from_ctor(
        &self,
        ctx: PatCtx,
        ctor_id: DeconstructedCtorId,
    ) -> DeconstructedPat {
        let fields = self.fields_ops().wildcards(ctx, ctor_id);

        DeconstructedPat::new(ctor_id, fields, ctx.ty, None)
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard(&self, ty: TermId) -> DeconstructedPat {
        let ctor = self.constructor_store().create(DeconstructedCtor::Wildcard);

        DeconstructedPat::new(ctor, Fields::empty(), ty, None)
    }

    /// Check whether this [DeconstructedPat] is an `or` pattern.
    pub(super) fn is_or_pat(&self, pat: &DeconstructedPat) -> bool {
        self.constructor_store().map_fast(pat.ctor, |ctor| matches!(ctor, DeconstructedCtor::Or))
    }

    /// Perform a `specialisation` on the current [DeconstructedPat]. This means
    /// that for a particular other constructor, this [DeconstructedPat]
    /// will be turned into multiple `specialised` variants of the
    /// constructor,
    pub(super) fn specialise(
        &self,
        ctx: PatCtx,
        pat: DeconstructedPatId,
        other_ctor_id: DeconstructedCtorId,
    ) -> SmallVec<[DeconstructedPatId; 2]> {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat(pat);
        let ctor = reader.get_deconstructed_ctor(pat.ctor);
        let other_ctor = reader.get_deconstructed_ctor(other_ctor_id);

        match (ctor, other_ctor) {
            (DeconstructedCtor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                self.fields_ops().wildcards(ctx, other_ctor_id).iter_patterns().copied().collect()
            }
            (DeconstructedCtor::List(this_list), DeconstructedCtor::List(other_list))
                if this_list.arity() != other_list.arity() =>
            {
                // If the arities mismatch, `this_list` must cover `other_list` and thus
                // it must be that `other_list` is a variable length list. Then, `other_list`
                // will have a guaranteed larger arity that `this_list`.
                //
                // So when specialising, we will fill the middle part of the `this_list` to
                // match the arity of the `other_list`.
                match this_list.kind {
                    ListKind::Fixed(_) => panic!("{:?} cannot cover {:?}", this_list, other_list),
                    ListKind::Var(prefix, suffix) => {
                        // we will need to get the inner `ty` of the list
                        let Some(inner_ty) = self.oracle().term_as_list(ctx.ty) else {
                            panic!("provided ty is not list as expected: {}", self.for_fmt(ctx.ty))
                        };

                        let prefix = pat.fields.fields[..prefix].to_vec();
                        let suffix = pat.fields.fields[this_list.arity() - suffix..].to_vec();

                        let wildcard = self.wildcard(inner_ty);

                        let extra_wildcards = other_list.arity() - this_list.arity();
                        let extra_wildcards = (0..extra_wildcards)
                            .map(|_| self.deconstructed_pat_store().create(wildcard.clone()))
                            .collect_vec();

                        prefix.into_iter().chain(extra_wildcards).chain(suffix).collect()
                    }
                }
            }
            _ => pat.fields.iter_patterns().copied().collect(),
        }
    }

    /// Report the spans of sub-patterns that were not reachable, if any.
    pub(super) fn unreachable_pats(&self, pat: &DeconstructedPat) -> Vec<PatId> {
        let mut pats = Vec::new();
        self.collect_unreachable_pats(pat, &mut pats);
        pats
    }

    /// Internal method to to recursively walk a [DeconstructedPat] and collect
    /// any [Span]s of patterns that were marked as unreachable.
    fn collect_unreachable_pats(&self, pat: &DeconstructedPat, spans: &mut Vec<PatId>) {
        // We don't look at sub-patterns if we
        // already reported the whole pattern as  unreachable.
        if !pat.is_reachable() && pat.id.is_some() {
            spans.push(pat.id.unwrap());
        } else {
            let reader = self.reader();

            for p in pat.fields.iter_patterns() {
                let p = reader.get_deconstructed_pat(*p);
                self.collect_unreachable_pats(&p, spans);
            }
        }
    }
}

impl PrepareForFormatting for DeconstructedPatId {}

impl Debug for ForFormatting<'_, DeconstructedPatId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pat = self.global_storage.deconstructed_pat_store.get(self.t);
        let ctor = self.global_storage.deconstructed_ctor_store.get(pat.ctor);

        // Utility for printing a joined list of things...
        let mut first = true;
        let mut start_or_continue = |s| {
            if first {
                first = false;
                ""
            } else {
                s
            }
        };

        match ctor {
            DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                let term = self.global_storage.term_store.get(pat.ty);

                // If it is a `struct` or an `enum` then try and get the
                // variant name...
                match term {
                    Term::Level1(Level1Term::NominalDef(nominal_def)) => {
                        match self.global_storage.nominal_def_store.get(nominal_def) {
                            NominalDef::Struct(struct_def) => {
                                if let Some(name) = struct_def.name {
                                    write!(f, "{}", name)?;
                                }
                            }
                            // @@EnumToUnion: remove and replace
                            NominalDef::Enum(_) => unreachable!(),
                        }
                    }
                    _ => panic!(
                        "Unexpected ty `{}` when printing deconstructed pat",
                        pat.ty.for_formatting(self.global_storage)
                    ),
                };

                write!(f, "(")?;

                for p in pat.fields.iter_patterns() {
                    write!(f, "{}", start_or_continue(", "))?;
                    write!(f, "{:?}", p.for_formatting(self.global_storage))?;
                }
                write!(f, ")")
            }
            DeconstructedCtor::IntRange(range) => write!(f, "{:?}", range),
            DeconstructedCtor::Str(value) => write!(f, "{}", value),
            DeconstructedCtor::List(list) => {
                let mut subpatterns = pat.fields.iter_patterns();

                write!(f, "[")?;

                match list.kind {
                    ListKind::Fixed(_) => {
                        for p in subpatterns {
                            write!(f, "{}{:?}", start_or_continue(", "), p)?;
                        }
                    }
                    ListKind::Var(prefix, _) => {
                        for p in subpatterns.by_ref().take(prefix) {
                            write!(
                                f,
                                "{}{:?}",
                                start_or_continue(", "),
                                p.for_formatting(self.global_storage)
                            )?;
                        }
                        write!(f, "{}", start_or_continue(", "))?;
                        write!(f, "..")?;
                        for p in subpatterns {
                            write!(
                                f,
                                "{}{:?}",
                                start_or_continue(", "),
                                p.for_formatting(self.global_storage)
                            )?;
                        }
                    }
                }

                write!(f, "]")
            }
            DeconstructedCtor::Or => {
                for pat in pat.fields.iter_patterns() {
                    write!(
                        f,
                        "{}{:?}",
                        start_or_continue(" | "),
                        pat.for_formatting(self.global_storage)
                    )?;
                }
                Ok(())
            }
            DeconstructedCtor::Wildcard
            | DeconstructedCtor::Missing
            | DeconstructedCtor::NonExhaustive => {
                write!(f, "_ : {}", pat.ty.for_formatting(self.global_storage))
            }
        }
    }
}
