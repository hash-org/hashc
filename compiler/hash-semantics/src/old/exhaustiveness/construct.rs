//! Exhaustiveness data structure to represent the `subject` of
//! a [`super::deconstruct::DeconstructedPat`]. [DeconstructedCtor]s
//! are a useful abstraction when performing the splitting and
//! specialisation operations on the deconstructed patterns.
//!
//! ## Splitting
//!
//! Splitting a constructor means to take the [DeconstructedCtor] and to
//! yield all the possible [DeconstructedCtor]s that can cover the
//! underlying constructors. For example, if the constructor
//! is specified as [DeconstructedCtor::Wildcard], we take the provided
//! [PatCtx] which stores the relevant term of the constructor and
//! produce a [DeconstructedCtor] that matches all possible cases of the
//! term. For example, if the term is `char` and the constructor
//! is [DeconstructedCtor::Wildcard], then the resultant constructors
//! becomes:
//!
//! ```ignore
//! [
//!     DeconstructedCtor::IntRange(0..=55295),      // 0..=D7FF
//!     DeconstructedCtor::IntRange(57344..=1114111) // E000..=10FFFF
//! ]
//! ```
//!
//! In other words, all the possible (valid) values of the `char` type.
//! A similar process occurs with all other wildcard types,
use std::fmt::Debug;

use hash_source::{
    constant::InternedStr,
    location::{SourceLocation, Span},
};
use hash_tir::old::{
    nominals::{NominalDef, StructFields},
    terms::{Level1Term, Term, TupleTy},
};
use hash_utils::store::{CloneStore, SequenceStoreKey, Store};
use smallvec::{smallvec, SmallVec};

use super::{
    range::{IntRange, SplitIntRange},
    AccessToUsefulnessOps, PatForFormatting, PreparePatForFormatting,
};
use crate::old::{
    diagnostics::macros::tc_panic,
    exhaustiveness::{
        list::{Array, ArrayKind, SplitVarList},
        PatCtx,
    },
    ops::AccessToOps,
    storage::{exhaustiveness::DeconstructedCtorId, AccessToStorage, StorageRef},
};

/// The [DeconstructedCtor] represents the type of constructor that a pattern
/// is.
///
/// @@Ranges: float ranges
#[derive(Debug, Clone, Copy)]
pub enum DeconstructedCtor {
    /// The constructor for patterns that have a single constructor, like
    /// tuples, struct patterns and fixed-length arrays.
    Single,

    /// Enum variants.
    Variant(usize),

    /// Ranges of integer literal values (`2`, `2..=5` or `2..5`).
    IntRange(IntRange),

    /// String literals.
    Str(InternedStr),

    /// Array patterns
    Array(Array),

    /// Wildcard pattern.
    Wildcard,

    /// Or-pattern.
    Or,

    /// Stands for constructors that are not seen in the matrix, as explained in
    /// the documentation for [super::wildcard::SplitWildcard].
    Missing,

    /// Declared as non-exhaustive
    NonExhaustive,
}

impl DeconstructedCtor {
    /// Check if the [DeconstructedCtor] is a wildcard.
    pub(super) fn is_wildcard(&self) -> bool {
        matches!(self, DeconstructedCtor::Wildcard)
    }

    /// Try and convert the [DeconstructedCtor] into a [IntRange].
    pub fn as_int_range(&self) -> Option<&IntRange> {
        match self {
            DeconstructedCtor::IntRange(range) => Some(range),
            _ => None,
        }
    }

    /// Try and convert the [DeconstructedCtor] into a [Array].
    pub fn as_array(&self) -> Option<&Array> {
        match self {
            DeconstructedCtor::Array(array) => Some(array),
            _ => None,
        }
    }
}

pub struct ConstructorOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for ConstructorOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> ConstructorOps<'tc> {
    /// Create a new [ConstructorOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Create a [SourceLocation] from a provided [Span].
    pub fn location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.local_storage().current_source() }
    }

    /// Compute the `arity` of this [DeconstructedCtor].
    pub(crate) fn arity(&self, ctx: PatCtx, ctor: DeconstructedCtorId) -> usize {
        match self.reader().get_deconstructed_ctor(ctor) {
            ctor @ (DeconstructedCtor::Single | DeconstructedCtor::Variant(_)) => {
                // we need to get term from the context here...
                //
                // if it a tuple, get the length and that is the arity
                // if it is a struct or enum, then we get that variant and
                // we can count the fields from that variant or struct.
                let reader = self.reader();

                // We need to extract the variant index from the constructor
                let variant_idx = match ctor {
                    DeconstructedCtor::Single => 0,
                    DeconstructedCtor::Variant(idx) => idx,
                    _ => unreachable!(),
                };

                reader.term_store().map_fast(ctx.ty, |ty| match ty {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => members.len(),
                    Term::Level1(Level1Term::NominalDef(def)) => {
                        reader.nominal_def_store().map_fast(*def, |def| match def {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                StructFields::Explicit(params) => params.len(),
                                StructFields::Opaque => 0,
                            },
                            NominalDef::Unit(_) => 0,
                            NominalDef::Enum(enum_def) => enum_def
                                .get_variant_by_idx(variant_idx)
                                .unwrap()
                                .fields
                                .map_or(0, |fields| fields.len()),
                        })
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        self,
                        "Unexpected ty `{}` when computing arity",
                        self.for_fmt(ctx.ty),
                    ),
                })
            }
            DeconstructedCtor::Array(list) => list.arity(),
            DeconstructedCtor::IntRange(_)
            | DeconstructedCtor::Str(_)
            | DeconstructedCtor::Wildcard
            | DeconstructedCtor::NonExhaustive
            | DeconstructedCtor::Missing => 0,
            DeconstructedCtor::Or => panic!("`Or` constructor doesn't have a fixed arity"),
        }
    }

    /// # Split a [DeconstructedCtor]
    ///
    /// Some constructors (namely `Wildcard`, `IntRange` and `List`) actually
    /// stand for a set of actual constructors (like variants, integers or
    /// fixed-sized list patterns).
    ///
    /// ## General
    ///
    /// When specialising for these constructors, we
    /// want to be specialising for the actual underlying constructors.
    /// Naively, we would simply return the list of constructors they correspond
    /// to. We instead are more clever: if there are constructors that we
    /// know will behave the same with reference to the current matrix, we keep
    /// them grouped. For example, all lists of a sufficiently large length
    /// will either be all useful or all non-useful with a given matrix.
    ///
    /// See the branches for details on how the splitting is done.
    ///
    /// ## Discarding constructors
    ///
    /// This function may discard some irrelevant constructors if this preserves
    /// behaviour and diagnostics. For example, for the `_` case, we ignore the
    /// constructors already present in the matrix, unless all of them are.
    pub(super) fn split(
        &self,
        ctx: PatCtx,
        ctor_id: DeconstructedCtorId,
        ctors: impl Iterator<Item = DeconstructedCtorId> + Clone,
    ) -> SmallVec<[DeconstructedCtorId; 1]> {
        let reader = self.reader();
        let ctor = reader.get_deconstructed_ctor(ctor_id);

        match ctor {
            DeconstructedCtor::Wildcard => {
                let mut wildcard = self.split_wildcard_ops().from(ctx);
                self.split_wildcard_ops().split(ctx, &mut wildcard, ctors);
                self.split_wildcard_ops().convert_into_ctors(ctx, wildcard)
            }
            // Fast track to just the single constructor if this range is trivial
            DeconstructedCtor::IntRange(range) if !range.is_singleton() => {
                let mut range = SplitIntRange::new(range);
                let int_ranges = ctors.filter_map(|c| {
                    self.constructor_store().map_fast(c, |c| c.as_int_range().cloned())
                });

                range.split(int_ranges);
                range
                    .iter()
                    .map(DeconstructedCtor::IntRange)
                    .map(|ctor| self.constructor_store().create(ctor))
                    .collect()
            }
            DeconstructedCtor::Array(Array { kind: ArrayKind::Var(prefix_len, suffix_len) }) => {
                let mut list = SplitVarList::new(prefix_len, suffix_len);

                let lists = ctors
                    .filter_map(|c| self.constructor_store().map_fast(c, |c| c.as_array().cloned()))
                    .map(|s| s.kind);
                list.split(lists);

                list.iter()
                    .map(DeconstructedCtor::Array)
                    .map(|ctor| self.constructor_store().create(ctor))
                    .collect()
            }
            // In any other case, the split just puts this constructor
            // into the resultant constructors since it cannot split it any
            // more...
            _ => smallvec![ctor_id],
        }
    }

    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a
    /// subset of `other`. For the simple cases, this is simply checking for
    /// equality. For the "grouped" constructors, this checks for inclusion.
    #[inline]
    pub fn is_covered_by(&self, ctor: &DeconstructedCtor, other: &DeconstructedCtor) -> bool {
        match (ctor, other) {
            // Wildcards cover anything
            (_, DeconstructedCtor::Wildcard) => true,
            // The missing ctors are not covered by anything in the matrix except wildcards.
            (DeconstructedCtor::Missing | DeconstructedCtor::Wildcard, _) => false,

            (DeconstructedCtor::Single, DeconstructedCtor::Single) => true,
            (DeconstructedCtor::Variant(self_id), DeconstructedCtor::Variant(other_id)) => {
                self_id == other_id
            }

            (DeconstructedCtor::IntRange(self_range), DeconstructedCtor::IntRange(other_range)) => {
                self_range.is_covered_by(other_range)
            }

            // It's safe to compare the `id`s of the allocated strings since they are
            // de-duplicated.
            (DeconstructedCtor::Str(self_str), DeconstructedCtor::Str(other_str)) => {
                self_str == other_str
            }

            (DeconstructedCtor::Array(self_slice), DeconstructedCtor::Array(other_slice)) => {
                self_slice.is_covered_by(*other_slice)
            }
            (DeconstructedCtor::NonExhaustive, _) => false,
            _ => {
                panic!("trying to compare incompatible constructors `{ctor:?}` and `{other:?}`")
            }
        }
    }

    /// Faster version of `is_covered_by` when applied to many constructors.
    /// `used_ctors` is assumed to be built from `matrix.head_ctors()` with
    /// wildcards filtered out, and `self` is assumed to have been split
    /// from a wildcard.
    pub(super) fn is_covered_by_any(
        &self,
        pat: DeconstructedCtorId,
        used_ctors: &[DeconstructedCtorId],
    ) -> bool {
        if used_ctors.is_empty() {
            return false;
        }

        let ctor = self.reader().get_deconstructed_ctor(pat);

        match ctor {
            // If `self` is `Single`, `used_ctors` cannot contain anything else than `Single`s.
            DeconstructedCtor::Single => !used_ctors.is_empty(),
            DeconstructedCtor::Variant(i) => used_ctors.iter().any(|c| {
                self.constructor_store()
                    .map_fast(*c, |c| matches!(c, DeconstructedCtor::Variant(k) if *k == i))
            }),
            DeconstructedCtor::IntRange(range) => used_ctors
                .iter()
                .filter_map(|c| {
                    self.constructor_store().map_fast(*c, |c| c.as_int_range().cloned())
                })
                .any(|other| range.is_covered_by(&other)),
            DeconstructedCtor::Array(list) => used_ctors
                .iter()
                .filter_map(|c| self.constructor_store().map_fast(*c, |c| c.as_array().cloned()))
                .any(|other| list.is_covered_by(other)),
            // This constructor is never covered by anything else
            DeconstructedCtor::NonExhaustive => false,
            DeconstructedCtor::Str(_)
            | DeconstructedCtor::Missing
            | DeconstructedCtor::Wildcard
            | DeconstructedCtor::Or => {
                panic!("Unexpected ctor in all_ctors")
            }
        }
    }
}

impl PreparePatForFormatting for DeconstructedCtorId {}

impl Debug for PatForFormatting<'_, DeconstructedCtorId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ctor = self.storage.exhaustiveness_storage().deconstructed_ctor_store.get(self.item);
        write!(f, "{ctor:?}")
    }
}
