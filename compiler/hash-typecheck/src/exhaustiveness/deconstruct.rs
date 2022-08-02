use std::cell::Cell;

use hash_source::location::Span;
use itertools::Itertools;
use smallvec::SmallVec;

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::structures::{List, ListKind, PatCtx},
    ops::AccessToOps,
    storage::{
        primitives::{
            ConstructedTerm, ConstructorId, DeconstructedPatId, Level0Term, Level1Term, NominalDef,
            Term, TermId, TupleLit,
        },
        AccessToStorage, StorageRef,
    },
};

use super::{
    construct::Constructor,
    fields::Fields,
    lower::{FieldPat, Pat, PatKind},
    AccessToUsefulnessOps,
};

/// A [DeconstructedPat] is a representation of a [Constructor] that is split
/// between the constructor subject `ctor` and the `fields` that the constructor
/// holds.
///
/// @@Todo: Implement `fmt` for the deconstructed pat as this is what will be
/// used         for displaying these patterns.
#[derive(Debug, Clone)]
pub struct DeconstructedPat {
    /// The subject of the [DeconstructedPat].
    pub ctor: ConstructorId,
    /// Any fields that are applying to the subject of the
    /// [DeconstructedPat]
    pub fields: Fields,
    /// The type of the current deconstructed pattern
    pub ty: TermId,
    /// The [Span] of the current pattern.
    pub span: Span,
    /// Whether the current pattern is reachable.
    pub reachable: Cell<bool>,
}

impl DeconstructedPat {
    pub(super) fn new(ctor: ConstructorId, fields: Fields, ty: TermId, span: Span) -> Self {
        DeconstructedPat { ctor, fields, span, ty, reachable: Cell::new(false) }
    }

    /// Clone this [DeconstructedPat] whilst also forgetting the reachability.
    pub(super) fn clone_and_forget_reachability(&self) -> Self {
        DeconstructedPat::new(self.ctor, self.fields.clone(), self.ty, self.span)
    }

    /// Expand an `or` pattern into a passed [Vec], whilst also
    /// applying the same operation on children patterns.
    pub fn expand<'p>(pat: &'p Pat, vec: &mut Vec<&'p Pat>) {
        if let PatKind::Or { pats } = pat.kind.as_ref() {
            for pat in pats {
                Self::expand(pat, vec);
            }
        } else {
            vec.push(pat)
        }
    }

    /// Internal use for expanding an [PatKind::Or] into children
    /// patterns. This will also expand any children that are `or`
    /// patterns.
    pub fn flatten_or_pat(pat: &Pat) -> Vec<&Pat> {
        let mut pats = Vec::new();
        Self::expand(pat, &mut pats);
        pats
    }

    /// Function to get the constructor of the [DeconstructedPat]
    pub(super) fn ctor(&self) -> ConstructorId {
        self.ctor
    }

    /// Function to get the `span` of the [DeconstructedPat]
    pub(super) fn span(&self) -> Span {
        self.span
    }

    /// Function to get the `ty` of the [DeconstructedPat]
    pub(super) fn ty(&self) -> TermId {
        self.ty
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

pub struct DeconstructPatOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for DeconstructPatOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> DeconstructPatOps<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    pub(super) fn wild_from_ctor(&self, ctx: PatCtx, ctor_id: ConstructorId) -> DeconstructedPat {
        let fields = self.fields_ops().wildcards(ctx, ctor_id);

        DeconstructedPat::new(ctor_id, fields, ctx.ty, Span::dummy())
    }

    /// Create a new wildcard [DeconstructedPat], primarily used when
    /// performing specialisations.
    pub(super) fn wildcard(&self, ty: TermId) -> DeconstructedPat {
        let ctor = self.constructor_store().create(Constructor::Wildcard);

        DeconstructedPat::new(ctor, Fields::empty(), ty, Span::dummy())
    }

    /// Check whether this [DeconstructedPat] is an `or` pattern.
    pub(super) fn is_or_pat(&self, pat: &DeconstructedPat) -> bool {
        self.constructor_store().map_unsafe(pat.ctor, |ctor| matches!(ctor, Constructor::Or))
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn from_pat(&self, ctx: PatCtx, pat: &Pat) -> DeconstructedPat {
        // @@Todo: support int, and float ranges
        let (ctor, fields) = match pat.kind.as_ref() {
            PatKind::Spread | PatKind::Wild => (Constructor::Wildcard, vec![]),
            PatKind::Constant { value } => {
                // This deals with `char` and `integer` types...
                let range = self.int_range_ops().range_from_constant(*value);
                (Constructor::IntRange(range), vec![])
            }
            PatKind::Str { value } => (Constructor::Str(*value), vec![]),
            PatKind::Variant { pats, .. } | PatKind::Leaf { pats } => {
                let reader = self.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level0(Level0Term::Tuple(TupleLit { members })) => {
                        let members = reader.get_args(*members).clone();

                        // Create wild-cards for all of the tuple inner members
                        let mut wilds: SmallVec<[_; 2]> = members
                            .positional()
                            .iter()
                            .map(|member| self.wildcard(member.value))
                            .collect();

                        for field in pats {
                            wilds[field.index] = self.from_pat(ctx, &field.pat);
                        }

                        (Constructor::Single, wilds.to_vec())
                    }
                    Term::Level0(Level0Term::Constructed(ConstructedTerm { members, .. })) => {
                        let ctor = match pat.kind.as_ref() {
                            PatKind::Variant { index, .. } => Constructor::Variant(*index),
                            PatKind::Leaf { .. } => Constructor::Single,
                            _ => unreachable!(),
                        };

                        let args = reader.get_args(*members);
                        let tys = args.positional().iter().map(|arg| arg.value);

                        let mut wilds: SmallVec<[_; 2]> = tys.map(|ty| self.wildcard(ty)).collect();

                        for field in pats {
                            wilds[field.index] = self.from_pat(ctx, &field.pat);
                        }

                        (ctor, wilds.to_vec())
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        self,
                        "Unexpected ty `{}` when deconstructing pattern {:?}",
                        self.for_fmt(ctx.ty),
                        pat
                    ),
                }
            }
            PatKind::List { prefix, spread, suffix } => {
                // If the list has a spread pattern, then it becomes variable
                // length, otherwise it remains as fixed-length.
                let kind = if spread.is_some() {
                    ListKind::Var(prefix.len(), suffix.len())
                } else {
                    ListKind::Fixed(prefix.len() + suffix.len())
                };

                let ctor = Constructor::List(List::new(kind));
                let fields =
                    prefix.iter().chain(suffix).map(|pat| self.from_pat(ctx, pat)).collect_vec();

                (ctor, fields)
            }
            PatKind::Or { .. } => {
                // here, we need to expand the or pattern, so that all of the
                // children patterns of the `or` become fields of the
                // deconstructed  pat.
                let pats = DeconstructedPat::flatten_or_pat(pat);

                let fields = pats.iter().map(|pat| self.from_pat(ctx, pat)).collect_vec();

                (Constructor::Or, fields)
            }
        };

        let ctor = self.constructor_store().create(ctor);

        // Now we need to put them in the slotmap...
        let fields = Fields::from_iter(
            fields.into_iter().map(|field| self.deconstructed_pat_store().create(field)),
        );

        DeconstructedPat::new(ctor, fields, ctx.ty, pat.span)
    }

    pub(crate) fn to_pat(&self, ctx: PatCtx, pat: DeconstructedPatId) -> Pat {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat(pat);
        let ctor = reader.get_ctor(pat.ctor());

        let children = pat.fields.iter_patterns().map(|p| self.to_pat(ctx, *p)).collect_vec();

        let kind = match ctor {
            ctor @ (Constructor::Single | Constructor::Variant(_)) => {
                let reader = self.reader();

                match reader.get_term(pat.ty) {
                    Term::Level0(Level0Term::Tuple(_)) => PatKind::Leaf {
                        pats: children
                            .into_iter()
                            .enumerate()
                            .map(|(index, pat)| FieldPat { index, pat })
                            .collect(),
                    },
                    Term::Level0(Level0Term::Constructed(ConstructedTerm { subject, .. })) => {
                        match reader.get_term(*subject) {
                            Term::Level1(Level1Term::NominalDef(id)) => {
                                let nominal_def = reader.get_nominal_def(*id);

                                let pats = children
                                    .into_iter()
                                    .enumerate()
                                    .map(|(index, pat)| FieldPat { index, pat })
                                    .collect_vec();

                                match nominal_def {
                                    NominalDef::Struct(_) => PatKind::Leaf { pats },
                                    NominalDef::Enum(_) => {
                                        let Constructor::Variant(index) = ctor else {
                                            unreachable!()
                                        };

                                        PatKind::Variant { def: *id, pats, index }
                                    }
                                }
                            }
                            _ => tc_panic!(
                                subject,
                                self,
                                "Malformed constructed subject during pattern conversion"
                            ),
                        }
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        self,
                        "Unexpected ty `{}` when converting to pattern",
                        self.for_fmt(ctx.ty),
                    ),
                }
            }
            Constructor::IntRange(range) => self.int_range_ops().to_pat_kind(&range, ctx),
            Constructor::Str(value) => PatKind::Str { value },
            Constructor::List(List { kind }) => match kind {
                ListKind::Fixed(_) => {
                    PatKind::List { prefix: children, spread: None, suffix: vec![] }
                }
                ListKind::Var(prefix, _) => {
                    let mut children = children.into_iter().peekable();

                    // build the prefix and suffix components
                    let prefix: Vec<_> = children.by_ref().take(prefix).collect();
                    let suffix: Vec<_> = children.collect();

                    // Create the `spread` dummy pattern
                    let spread = Pat {
                        span: Span::dummy(),
                        kind: Box::new(PatKind::Spread),
                        has_guard: false,
                    };

                    PatKind::List { prefix, spread: Some(spread), suffix }
                }
            },
            Constructor::Wildcard | Constructor::NonExhaustive => PatKind::Wild,
            Constructor::Or => panic!(
                "cannot convert an `or` deconstructed pat back into pat"
            ),
            Constructor::Missing => panic!(
                "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug,             
                `Missing` should have been processed in `apply_constructors`"
            ),
        };

        Pat { span: pat.span, kind: Box::new(kind), has_guard: false }
    }

    /// Perform a `specialisation` on the current [DeconstructedPat]. This means
    /// that for a particular other constructor, this [DeconstructedPat]
    /// will be turned into multiple `specialised` variants of the
    /// constructor,
    pub(super) fn specialise(
        &mut self,
        ctx: PatCtx,
        pat: DeconstructedPatId,
        other_ctor_id: ConstructorId,
    ) -> SmallVec<[DeconstructedPatId; 2]> {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat(pat);
        let ctor = reader.get_ctor(pat.ctor());
        let other_ctor = reader.get_ctor(other_ctor_id);

        match (ctor, other_ctor) {
            (Constructor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                self.fields_ops().wildcards(ctx, other_ctor_id).iter_patterns().copied().collect()
            }
            (Constructor::List(self_list), Constructor::List(other_list))
                if self_list.arity() != other_list.arity() =>
            {
                // If the arities mismatch, `self_list` must cover `other_list` and thus
                // it must be that `other_list` is a variable length list. Then, `other_list`
                // will have a guaranteed larger arity that `self_list`.
                //
                // So when specialising, we will fill the middle part of the `self_list` to
                // match the arity of the `other_list`.
                match self_list.kind {
                    ListKind::Fixed(_) => panic!("{:?} cannot cover {:?}", self_list, other_list),
                    ListKind::Var(_prefix, _suffix) => {
                        // @@Todo: we will need to get the inner `ty` of the list

                        // let prefix = &pat.fields.fields[..prefix];
                        // let suffix = &pat.fields.fields[self_list.arity() - suffix..];

                        todo!()
                        // let wildcard: &_ = &DeconstructedPat::wildcard();

                        // let extra_wildcards = other_list.arity() -
                        // self_list.arity();
                        // let extra_wildcards = (0..extra_wildcards).map(|_|
                        // wildcard); prefix.iter().
                        // chain(extra_wildcards).chain(suffix).collect()
                    }
                }
            }
            _ => pat.fields.iter_patterns().copied().collect(),
        }
    }

    /// Report the spans of sub-patterns that were not reachable, if any.
    pub(super) fn unreachable_spans(&self, pat: &DeconstructedPat) -> Vec<Span> {
        let mut spans = Vec::new();
        self.collect_unreachable_spans(pat, &mut spans);
        spans
    }

    /// Internal method to to recursively walk a [DeconstructedPat] and collect
    /// any [Span]s of patterns that were marked as unreachable.
    fn collect_unreachable_spans(&self, pat: &DeconstructedPat, spans: &mut Vec<Span>) {
        // We don't look at sub-patterns if we
        // already reported the whole pattern as  unreachable.
        if !pat.is_reachable() {
            spans.push(pat.span);
        } else {
            let reader = self.reader();

            for p in pat.fields.iter_patterns() {
                let p = reader.get_deconstructed_pat(*p);
                self.collect_unreachable_spans(&p, spans);
            }
        }
    }
}
