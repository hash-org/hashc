//! This file contains logic surrounding [DeconstructedPat] which is a
//! representation of a [hash_tir::old::Pat]  that is deconstructed and
//! simplified to the point of being processable by the  usefulness algorithm. A
//! [DeconstructedPat] is essentially a tree representation of a `pat` with any
//! of the inner fields of the pat being represented as child
//! [DeconstructedPat]s stored within the  `fields` parameter of the structure.
use std::{
    cell::Cell,
    fmt::{self, Debug},
};

use hash_storage::store::statics::StoreId;
use hash_tir::{
    intrinsics::utils::try_use_ty_as_array_ty,
    tir::{CtorDefId, DataTy, NodesId, PatId, Ty, TyId},
};
use hash_utils::{itertools::Itertools, smallvec::SmallVec};

use super::{construct::DeconstructedCtor, fields::Fields};
use crate::{
    ExhaustivenessChecker, ExhaustivenessEnv, ExhaustivenessFmtCtx, PatCtx,
    list::ArrayKind,
    range::IntRangeWithBias,
    storage::{DeconstructedCtorId, DeconstructedPatId},
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
    pub ty: TyId,

    /// An associated [hash_tir::tir::Pat] which is used to
    /// link a particular pattern with a span. This is primarily
    /// used for reporting reachability, or checking if integer  
    /// ranges overlap.
    ///
    /// @@Sizing: it would be nice to avoid the option so we could
    /// shrink the constructor down from `32bytes` to `24bytes`.
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
        ty: TyId,
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

impl<E: ExhaustivenessEnv> ExhaustivenessChecker<'_, E> {
    /// Create a `match-all` [DeconstructedPat] and infer [Fields] as
    /// from the provided type in the context, this is only to be used
    /// when creating `match-all` wildcard patterns.
    pub(super) fn wildcard_from_ctor(
        &mut self,
        ctx: PatCtx,
        ctor_id: DeconstructedCtorId,
    ) -> DeconstructedPat {
        let fields = self.wildcards_from_ctor(ctx, ctor_id);

        DeconstructedPat::new(ctor_id, fields, ctx.ty, None)
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard_from_ty(&mut self, ty: TyId) -> DeconstructedPat {
        let ctor = self.make_ctor(DeconstructedCtor::Wildcard);
        DeconstructedPat::new(ctor, Fields::empty(), ty, None)
    }

    /// Check whether this [DeconstructedPat] is an `or` pattern.
    pub(super) fn is_or_pat(&self, pat: &DeconstructedPat) -> bool {
        matches!(self.get_ctor(pat.ctor), DeconstructedCtor::Or)
    }

    /// Perform a `specialisation` on the current [DeconstructedPat]. This means
    /// that for a particular other constructor, this [DeconstructedPat]
    /// will be turned into multiple `specialised` variants of the
    /// constructor,
    pub(super) fn specialise(
        &mut self,
        ctx: PatCtx,
        pat_id: DeconstructedPatId,
        other_ctor_id: DeconstructedCtorId,
    ) -> SmallVec<[DeconstructedPatId; 2]> {
        let pat = self.get_pat(pat_id);
        let pat_ctor = self.get_ctor(pat.ctor);
        let other_ctor = self.get_ctor(other_ctor_id);

        match (pat_ctor, other_ctor) {
            (DeconstructedCtor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                self.wildcards_from_ctor(ctx, other_ctor_id).iter_patterns().collect()
            }
            (DeconstructedCtor::Array(this_list), DeconstructedCtor::Array(other_list))
                if this_list.arity() != other_list.arity() =>
            {
                // If the arities mismatch, `this_list` must cover `other_list` and thus
                // it must be that `other_list` is a variable length list. Then, `other_list`
                // will have a guaranteed larger arity that `this_list`.
                //
                // So when specialising, we will fill the middle part of the `this_list` to
                // match the arity of the `other_list`.
                match this_list.kind {
                    ArrayKind::Fixed(_) => panic!("{this_list:?} cannot cover {other_list:?}"),
                    ArrayKind::Var(prefix, suffix) => {
                        let array_ty = try_use_ty_as_array_ty(ctx.ty).unwrap();
                        let this_arity = this_list.arity();
                        let other_arity = other_list.arity();

                        let prefix = pat.fields.fields[..prefix].to_vec();
                        let suffix = pat.fields.fields[this_arity - suffix..].to_vec();

                        let wildcard = self.wildcard_from_ty(array_ty.element_ty);

                        let extra_wildcards = other_arity - this_arity;
                        let extra_wildcards = (0..extra_wildcards)
                            .map(|_| self.make_pat(wildcard.clone()))
                            .collect_vec();

                        prefix.into_iter().chain(extra_wildcards).chain(suffix).collect()
                    }
                }
            }
            _ => pat.fields.iter_patterns().collect(),
        }
    }

    /// Report the spans of sub-patterns that were not reachable, if any.
    pub(super) fn compute_unreachable_pats(&self, pat: &DeconstructedPat) -> Vec<PatId> {
        let mut pats = Vec::new();
        self.collect_unreachable_pats(pat, &mut pats);
        pats
    }

    /// Internal method to to recursively walk a [DeconstructedPat] and collect
    /// any [PatId]s of patterns that were marked as unreachable.
    fn collect_unreachable_pats(&self, pat: &DeconstructedPat, spans: &mut Vec<PatId>) {
        // We don't look at sub-patterns if we
        // already reported the whole pattern as  unreachable.
        if !pat.is_reachable() && pat.id.is_some() {
            spans.push(pat.id.unwrap());
        } else {
            for p in pat.fields.iter_patterns() {
                let p = self.get_pat(p);
                self.collect_unreachable_pats(p, spans);
            }
        }
    }
}

impl<E: ExhaustivenessEnv> fmt::Debug for ExhaustivenessFmtCtx<'_, DeconstructedPatId, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

        let pat = self.checker.get_pat(self.item);
        let ctor = self.checker.get_ctor(pat.ctor);

        match ctor {
            DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                match *pat.ty.value() {
                    Ty::TupleTy(_) => {}
                    Ty::DataTy(ty @ DataTy { data_def, .. }) => {
                        write!(f, "{ty}")?;

                        // If we have a variant, we print the specific variant that is
                        // currently active.
                        if let DeconstructedCtor::Variant(index) = ctor {
                            let ctors = data_def.borrow().ctors.assert_defined();
                            let ctor_name = CtorDefId::new(ctors.elements(), *index).borrow().name;
                            write!(f, "::{ctor_name}")?;
                        }
                    }
                    _ => {
                        panic!("unexpected ty `{}` when printing deconstructed pat", pat.ty)
                    }
                };

                write!(f, "(")?;

                for p in pat.fields.iter_patterns() {
                    write!(f, "{}", start_or_continue(", "))?;
                    write!(f, "{:?}", self.with(p))?;
                }
                write!(f, ")")
            }
            DeconstructedCtor::IntRange(range) => {
                // Convert the type into a ReprTy
                let ty = self.checker.ty_lower().repr_ty_from_tir_ty(pat.ty);
                let bias = self.checker.signed_bias(ty);
                write!(f, "{:?}", IntRangeWithBias::new(*range, bias))
            }
            DeconstructedCtor::Str(value) => write!(f, "{}", value.to_str()),
            DeconstructedCtor::Array(list) => {
                let mut sub_patterns = pat.fields.iter_patterns();

                write!(f, "[")?;

                match list.kind {
                    ArrayKind::Fixed(_) => {
                        for p in sub_patterns {
                            write!(f, "{}{p:?}", start_or_continue(","))?;
                        }
                    }
                    ArrayKind::Var(prefix, _) => {
                        for p in sub_patterns.by_ref().take(prefix) {
                            write!(f, "{}{:?}", start_or_continue(", "), self.with(p))?;
                        }
                        write!(f, "{}", start_or_continue(", "))?;
                        write!(f, "..")?;
                        for p in sub_patterns {
                            write!(f, "{}{:?}", start_or_continue(", "), self.with(p))?;
                        }
                    }
                }

                write!(f, "]")
            }
            DeconstructedCtor::Or => {
                for pat in pat.fields.iter_patterns() {
                    write!(f, "{}{:?}", start_or_continue(" | "), self.with(pat))?;
                }
                Ok(())
            }
            ctor @ (DeconstructedCtor::Wildcard
            | DeconstructedCtor::Missing
            | DeconstructedCtor::NonExhaustive) => {
                // Just for clarity, we want to also print what specific `wildcard`
                // constructor it is
                let prefix = match ctor {
                    DeconstructedCtor::Wildcard => "_",
                    DeconstructedCtor::Missing => "?",
                    DeconstructedCtor::NonExhaustive => "∞",
                    _ => unreachable!(),
                };

                write!(f, "{prefix} : {}", pat.ty)
            }
        }
    }
}
