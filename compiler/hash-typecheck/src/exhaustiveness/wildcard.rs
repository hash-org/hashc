//! This file contains logic for splitting [DeconstructedCtor]s that
//! are of the variant [DeconstructedCtor::Wildcard]. In this situation
//! the `splitting` operation creates [DeconstructedCtor]s that represent
//! the whole range of all possible values by the associated type
//! to the constructor.
use hash_ast::ast::{IntTy, RangeEnd};
use smallvec::{smallvec, SmallVec};

use crate::{
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, Level1Term, NominalDef, Term},
        AccessToStorage, StorageRef,
    },
};

/// A [DeconstructedCtor::Wildcard] that we split relative to the constructors
/// in the matrix.
///
/// A constructor that is not present in the matrix rows will only be covered by
/// the rows that have wildcards. Thus we can group all of those constructors
/// together; we call them "missing constructors". Splitting a wildcard would
/// therefore list all present constructors individually (or grouped if they are
/// integers or slices), and then all missing constructors together as a group.
///
/// However we can go further: since any constructor will match the wildcard
/// rows, and having more rows can only reduce the amount of usefulness
/// witnesses, we can skip the present constructors and only try the missing
/// ones. This will not preserve the whole list of witnesses, but will preserve
/// whether the list is empty or not. In fact this is quite natural from the
/// point of view of diagnostics too. This is done in `convert_into_ctors`:
/// in some cases we only return `Missing`.
#[derive(Debug)]
pub struct SplitWildcard {
    /// Constructors seen in the matrix.
    pub matrix_ctors: Vec<ConstructorId>,
    /// All the constructors for this type
    pub all_ctors: SmallVec<[ConstructorId; 1]>,
}

use super::{
    construct::DeconstructedCtor,
    list::{List, ListKind},
    AccessToUsefulnessOps,
};

pub struct SplitWildcardOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for SplitWildcardOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> SplitWildcardOps<'tc> {
    /// Create a new [SplitWildcardOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Create a [SplitWildcard] from the current context.
    pub(super) fn from(&mut self, ctx: PatCtx) -> SplitWildcard {
        let reader = self.reader();

        let make_range = |start, end| {
            DeconstructedCtor::IntRange(self.int_range_ops().make_range(
                ctx,
                start,
                end,
                &RangeEnd::Included,
            ))
        };

        // This determines the set of all possible constructors for the type `ctx.ty`.
        // For numbers, lists we use ranges and variable-length lists when appropriate.
        //
        // we need make sure to omit constructors that are statically impossible. E.g.,
        // for `Option<!>`, we do not include `Some(_)` in the returned list of
        // constructors.
        let all_ctors = if let Some(int_kind) = self.oracle().term_as_int(ctx.ty) {
            match int_kind {
                // @@Future: Maybe in the future, we can have a compiler setting/project
                // setting that allows a user to say `it's ok to use the `target` pointer width`
                IntTy::ISize | IntTy::USize | IntTy::UBig | IntTy::IBig => {
                    smallvec![DeconstructedCtor::NonExhaustive]
                }
                kind if kind.is_signed() => {
                    // Safe to unwrap since we deal with `ibig` and `ubig` variants...
                    let size = kind.size().unwrap();
                    let bits = size * 8;

                    let min = 1u128 << (bits - 1);
                    let max = min - 1;

                    // i_kind::MIN..=_kind::MAX
                    smallvec![make_range(min, max)]
                }
                kind => {
                    // Safe to unwrap since we deal with `ibig` and `ubig` variants...
                    let size = kind.size().unwrap();
                    let bits = size * 8;

                    let shift = 128 - bits;

                    // Truncate (shift left to drop out leftover values, shift right to fill with
                    // zeroes).
                    let max = (u128::MAX << shift) >> shift;

                    smallvec![make_range(0, max)]
                }
            }
        } else if self.oracle().term_as_list(ctx.ty).is_some() {
            // For lists, we just default to a variable length list
            smallvec![DeconstructedCtor::List(List { kind: ListKind::Var(0, 0) })]
        } else {
            match ctx.ty {
                ty if self.oracle().term_is_char(ty) => {
                    smallvec![
                        // The valid Unicode Scalar Value ranges.
                        make_range('\u{0000}' as u128, '\u{D7FF}' as u128),
                        make_range('\u{E000}' as u128, '\u{10FFFF}' as u128),
                    ]
                }
                ty if self.oracle().term_is_never(ty) => {
                    // If our subject is the never type, we cannot
                    // expose its emptiness. The exception is if the pattern
                    // is at the top level, because we want empty matches
                    // to be considered exhaustive.
                    if !ctx.is_top_level {
                        smallvec![DeconstructedCtor::NonExhaustive]
                    } else {
                        smallvec![]
                    }
                }
                ty => match reader.get_term(ty) {
                    Term::Level1(Level1Term::NominalDef(def)) => {
                        match reader.get_nominal_def(*def) {
                            NominalDef::Struct(_) => smallvec![DeconstructedCtor::Single],
                            NominalDef::Enum(enum_def) => {
                                // The exception is if the pattern is at the top level, because we
                                // want empty matches to be
                                // considered exhaustive.
                                let is_secretly_empty =
                                    enum_def.variants.is_empty() && !ctx.is_top_level;

                                let mut ctors: SmallVec<[_; 1]> = enum_def
                                    .variants
                                    .iter()
                                    .enumerate()
                                    .map(|(index, _)| DeconstructedCtor::Variant(index))
                                    .collect();

                                if is_secretly_empty {
                                    ctors.push(DeconstructedCtor::NonExhaustive);
                                }

                                ctors
                            }
                        }
                    }
                    Term::Level1(Level1Term::Tuple(_)) => smallvec![DeconstructedCtor::Single],
                    _ => smallvec![DeconstructedCtor::NonExhaustive],
                },
            }
        };

        // Now we have to allocate `all_ctors` into storage
        let all_ctors =
            all_ctors.into_iter().map(|ctor| self.constructor_store().create(ctor)).collect();

        SplitWildcard { matrix_ctors: Vec::new(), all_ctors }
    }

    /// Perform a split on a [SplitWildcard], take `all_ctors` on the
    /// current [SplitWildcard] and split them with the provided constructors.
    pub(super) fn split(
        &mut self,
        ctx: PatCtx,
        ctor: &mut SplitWildcard,
        ctors: impl Iterator<Item = ConstructorId> + Clone,
    ) {
        // Since `all_ctors` never contains wildcards, this won't recurse further.
        ctor.all_ctors = ctor
            .all_ctors
            .iter()
            .flat_map(|ctor| self.constructor_ops().split(ctx, *ctor, ctors.clone()))
            .collect();

        ctor.matrix_ctors = ctors
            .filter(|c| !self.constructor_store().map_unsafe(*c, |c| c.is_wildcard()))
            .collect();
    }

    /// Whether there are any value constructors for this type that are not
    /// present in the matrix.
    fn any_missing(&self, wildcard: &SplitWildcard) -> bool {
        self.iter_missing(wildcard).next().is_some()
    }

    /// Iterate over the constructors for this type that are not present in the
    /// matrix.
    pub(super) fn iter_missing<'a>(
        &'a self,
        wildcard: &'a SplitWildcard,
    ) -> impl Iterator<Item = ConstructorId> + 'a {
        wildcard.all_ctors.iter().copied().filter(move |ctor| {
            !self.constructor_ops().is_covered_by_any(*ctor, &wildcard.matrix_ctors)
        })
    }

    /// Convert the current [SplitWildcard] into it's respective constructors.
    ///
    /// In the case that the wildcard has missing constructors, it is at the
    /// top level, and the row type is not of an integral kind then we will
    /// use the [DeconstructedCtor::Missing] variant, otherwise falling back to
    /// [DeconstructedCtor::Wildcard] in the situations where it is nonsensical
    /// to show all missing constructors.
    pub(super) fn convert_into_ctors(
        &self,
        ctx: PatCtx,
        wildcard: SplitWildcard,
    ) -> SmallVec<[ConstructorId; 1]> {
        // If Some constructors are missing, thus we can specialise with the special
        // `Missing` constructor, which stands for those constructors that are
        // not seen in the matrix, and matches the same rows as any of them
        // (namely the wildcard rows). See the top of the file for details.
        if self.any_missing(&wildcard) {
            // If some constructors are missing, we typically want to report those
            // constructors, e.g.:
            // ```ignore
            //     Direction := enum(N, S, E, W);
            //
            //     dir := Direction::N;
            //     match dir {
            //         Direction::N => ...;
            //     }
            // ```
            // we can report 3 witnesses: `S`, `E`, and `W`.
            //
            // However, if the user didn't actually specify a constructor
            // in this arm, e.g., in
            // ```
            //     x: (Direction, Direction, bool) = ...;
            //     (_, _, false) := x;
            // ```
            // we don't want to show all 16 possible witnesses `(<direction-1>,
            // <direction-2>, true)` - we are satisfied with `(_, _, true)`. So
            // if all constructors are missing we prefer to report just a
            // wildcard `_`.
            //
            // The exception is: if we are at the top-level, for example in an empty match,
            // we sometimes prefer reporting the list of constructors instead of
            // just `_`.
            let ctor = if !wildcard.matrix_ctors.is_empty()
                || (ctx.is_top_level && self.oracle().term_as_int(ctx.ty).is_none())
            {
                DeconstructedCtor::Missing
            } else {
                DeconstructedCtor::Wildcard
            };

            let ctor = self.constructor_store().create(ctor);
            return smallvec![ctor];
        }

        wildcard.all_ctors
    }
}
