//! Exhaustiveness data structure to represent the `subject` of
//! a [`super::deconstruct::DeconstructedPat`]. [Constructor]s
//! are a useful abstraction when performing the splitting and
//! specialisation operations on the deconstructed patterns.
//!
//! ## Splitting
//!
//! Splitting a constructor means to take the [Constructor] and to
//! yield all the possible [Constructor]s that can cover the
//! underlying constructors. For example, if the constructor
//! is specified as [Constructor::Wildcard], we take the provided
//! [PatCtx] which stores the relevant term of the constructor and
//! produce a [Constructor] that matches all possible cases of the
//! term. For example, if the term is `char` and the constructor
//! is [Constructor::Wildcard], then the resultant constructors
//! becomes:
//!
//! ```ignore
//! [
//!     Constructor::IntRange(0..=55295),      // 0..=D7FF
//!     Constructor::IntRange(57344..=1114111) // E000..=10FFFF
//! ]
//! ```
//!
//! In other words, all the possible (valid) values of the `char` type.
//! A similar process occurs with all other wildcard types,
use hash_reporting::macros::panic_on_span;
use hash_source::{
    location::{SourceLocation, Span},
    string::Str,
};
use smallvec::{smallvec, SmallVec};

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::{
        list::{List, ListKind, SplitVarList},
        PatCtx,
    },
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, Level1Term, NominalDef, StructFields, Term, TupleTy},
        AccessToStorage, StorageRef,
    },
};

use super::{
    range::{IntRange, SplitIntRange},
    AccessToUsefulnessOps,
};

/// The [Constructor] represents the type of constructor that a pattern
/// is.
///
/// @@Ranges: float ranges
#[derive(Debug, Clone)]
pub enum Constructor {
    /// The constructor for patterns that have a single constructor, like
    /// tuples, struct patterns and fixed-length arrays.
    Single,
    /// Enum variants.
    Variant(usize),
    /// Ranges of integer literal values (`2`, `2..=5` or `2..5`).
    IntRange(IntRange),
    /// String literals.
    Str(Str),
    /// List patterns
    List(List),
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

impl Constructor {
    /// Check if the [Constructor] is a wildcard.
    pub(super) fn is_wildcard(&self) -> bool {
        matches!(self, Constructor::Wildcard)
    }

    /// Try and convert the [Constructor] into a [IntRange].
    pub fn as_int_range(&self) -> Option<&IntRange> {
        match self {
            Constructor::IntRange(range) => Some(range),
            _ => None,
        }
    }

    /// Try and convert the [Constructor] into a [List].
    pub fn as_list(&self) -> Option<&List> {
        match self {
            Constructor::List(list) => Some(list),
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
        SourceLocation { span, source_id: self.local_storage().current_source() }
    }

    /// Compute the `arity` of this [Constructor].
    pub(crate) fn arity(&self, ctx: PatCtx, ctor: ConstructorId) -> usize {
        let reader = self.reader();

        match reader.get_ctor(ctor) {
            Constructor::Single | Constructor::Variant(_) => {
                // we need to get term from the context here...
                //
                // if it a tuple, get the length and that is the arity
                // if it is a struct or enum, then we get that variant and
                // we can count the fields from that variant or struct.
                let reader = self.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        reader.get_params(*members).len()
                    }
                    Term::Level1(Level1Term::NominalDef(def)) => {
                        match reader.get_nominal_def(*def) {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                StructFields::Explicit(params) => reader.get_params(params).len(),
                                StructFields::Opaque => 0,
                            },
                            // @@Remove: when enums are no longer represented as thi
                            NominalDef::Enum(_) => unreachable!(),
                        }
                    }
                    _ => tc_panic!(
                        ctx.ty,
                        self,
                        "Unexpected ty `{}` when computing arity",
                        self.for_fmt(ctx.ty),
                    ),
                }
            }
            Constructor::List(list) => list.arity(),
            Constructor::IntRange(_)
            | Constructor::Str(_)
            | Constructor::Wildcard
            | Constructor::NonExhaustive
            | Constructor::Missing => 0,
            Constructor::Or => panic!("`Or` constructor doesn't have a fixed arity"),
        }
    }

    /// # Split a [Constructor]
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
        ctor_id: ConstructorId,
        ctors: impl Iterator<Item = ConstructorId> + Clone,
    ) -> SmallVec<[ConstructorId; 1]> {
        let reader = self.reader();
        let ctor = reader.get_ctor(ctor_id);

        match ctor {
            Constructor::Wildcard => {
                let mut wildcard = self.split_wildcard_ops().from(ctx);
                self.split_wildcard_ops().split(ctx, &mut wildcard, ctors);
                self.split_wildcard_ops().convert_into_ctors(ctx, wildcard)
            }
            // Fast track to just the single constructor if this range is trivial
            Constructor::IntRange(range) if !range.is_singleton() => {
                // @@Ranges: this is only used when `range` patterns are a thing

                let mut range = SplitIntRange::new(range);
                let int_ranges = ctors.filter_map(|c| {
                    self.constructor_store().map_unsafe(c, |c| c.as_int_range().cloned())
                });

                range.split(int_ranges);
                range
                    .iter()
                    .map(Constructor::IntRange)
                    .map(|ctor| self.constructor_store().create(ctor))
                    .collect()
            }
            Constructor::List(List { kind: ListKind::Var(prefix_len, suffix_len) }) => {
                let mut list = SplitVarList::new(prefix_len, suffix_len);

                let lists = ctors
                    .filter_map(|c| {
                        self.constructor_store().map_unsafe(c, |c| c.as_list().cloned())
                    })
                    .map(|s| s.kind);
                list.split(lists);

                list.iter()
                    .map(Constructor::List)
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
    pub fn is_covered_by(&self, ctx: PatCtx, ctor: &Constructor, other: &Constructor) -> bool {
        match (ctor, other) {
            // Wildcards cover anything
            (_, Constructor::Wildcard) => true,
            // The missing ctors are not covered by anything in the matrix except wildcards.
            (Constructor::Missing | Constructor::Wildcard, _) => false,

            (Constructor::Single, Constructor::Single) => true,
            (Constructor::Variant(self_id), Constructor::Variant(other_id)) => self_id == other_id,

            (Constructor::IntRange(self_range), Constructor::IntRange(other_range)) => {
                self_range.is_covered_by(other_range)
            }

            // It's safe to compare the `id`s of the allocated strings since they are
            // de-duplicated.
            (Constructor::Str(self_str), Constructor::Str(other_str)) => self_str == other_str,

            (Constructor::List(self_slice), Constructor::List(other_slice)) => {
                self_slice.is_covered_by(*other_slice)
            }
            (Constructor::NonExhaustive, _) => false,

            _ => panic_on_span!(
                self.location(ctx.span),
                self.source_map(),
                "trying to compare incompatible constructors {:?} and {:?}",
                ctor,
                other
            ),
        }
    }

    /// Faster version of `is_covered_by` when applied to many constructors.
    /// `used_ctors` is assumed to be built from `matrix.head_ctors()` with
    /// wildcards filtered out, and `self` is assumed to have been split
    /// from a wildcard.
    pub(super) fn is_covered_by_any(
        &self,
        ctor: ConstructorId,
        used_ctors: &[ConstructorId],
    ) -> bool {
        if used_ctors.is_empty() {
            return false;
        }

        let ctor = self.reader().get_ctor(ctor);

        match ctor {
            // If `self` is `Single`, `used_ctors` cannot contain anything else than `Single`s.
            Constructor::Single => !used_ctors.is_empty(),
            Constructor::Variant(i) => used_ctors.iter().any(|c| {
                self.constructor_store()
                    .map_unsafe(*c, |c| matches!(c, Constructor::Variant(k) if *k == i))
            }),
            Constructor::IntRange(range) => used_ctors
                .iter()
                .filter_map(|c| {
                    self.constructor_store().map_unsafe(*c, |c| c.as_int_range().cloned())
                })
                .any(|other| range.is_covered_by(&other)),
            Constructor::List(list) => used_ctors
                .iter()
                .filter_map(|c| self.constructor_store().map_unsafe(*c, |c| c.as_list().cloned()))
                .any(|other| list.is_covered_by(other)),
            // This constructor is never covered by anything else
            Constructor::NonExhaustive => false,
            Constructor::Str(_)
            | Constructor::Missing
            | Constructor::Wildcard
            | Constructor::Or => {
                panic!("Unexpected ctor in all_ctors")
            }
        }
    }
}