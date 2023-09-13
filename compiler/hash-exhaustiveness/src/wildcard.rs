//! This file contains logic for splitting [DeconstructedCtor]s that
//! are of the variant [DeconstructedCtor::Wildcard]. In this situation
//! the `splitting` operation creates [DeconstructedCtor]s that represent
//! the whole range of all possible values by the associated type
//! to the constructor.
use hash_ast::ast::RangeEnd;
use hash_storage::store::{statics::StoreId, SequenceStoreKey, Store, TrivialSequenceStoreKey};
use hash_target::size::Size;
use hash_tir::{
    data::{DataDefCtors, DataTy, NumericCtorBits, PrimitiveCtorInfo},
    intrinsics::utils::try_use_ty_as_int_ty,
    terms::Ty,
};
use hash_utils::smallvec::{smallvec, SmallVec};

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
    pub matrix_ctors: Vec<DeconstructedCtorId>,
    /// All the constructors for this type
    pub all_ctors: SmallVec<[DeconstructedCtorId; 1]>,
}

use super::{
    construct::DeconstructedCtor,
    list::{Array, ArrayKind},
};
use crate::{storage::DeconstructedCtorId, ExhaustivenessChecker, ExhaustivenessEnv, PatCtx};

impl<E: ExhaustivenessEnv> ExhaustivenessChecker<'_, E> {
    /// Create a [SplitWildcard] from the current context.
    pub(super) fn split_wildcard_from_pat_ctx(&self, ctx: PatCtx) -> SplitWildcard {
        let make_range = |start, end| {
            DeconstructedCtor::IntRange(self.make_int_range(
                ctx.ty,
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
        let all_ctors = match *ctx.ty.value() {
            Ty::DataTy(DataTy { data_def, .. }) => {
                let def = data_def.value();

                match def.ctors {
                    DataDefCtors::Defined(ctors) => {
                        if ctors.len() == 1 {
                            smallvec![DeconstructedCtor::Single]
                        } else {
                            // The exception is if the pattern is at the top level, because
                            // we want empty matches to
                            // be considered exhaustive.
                            let is_secretly_empty = ctors.value().is_empty() && !ctx.is_top_level;

                            let mut ctors: SmallVec<[_; 1]> = ctors
                                .value()
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
                    DataDefCtors::Primitive(ctor) => match ctor {
                        PrimitiveCtorInfo::Numeric(ctor_info) => {
                            if let NumericCtorBits::Bounded(bits) = ctor_info.bits && !ctor_info.is_float {
                                if ctor_info.is_signed {
                                    let min = 1u128 << (bits - 1);
                                    let max = min - 1;

                                    // i_kind::MIN..=_kind::MAX
                                    smallvec![make_range(min, max)]
                                } else {
                                    let size = Size::from_bits(bits as u64);
                                    let max = size.truncate(u128::MAX);

                                    smallvec![make_range(0, max)]
                                }
                            } else {
                                // This is then either a `ubig` or `ibig` which are un-bounded and
                                // hence non-exhaustive.
                                smallvec![DeconstructedCtor::NonExhaustive]
                            }
                        }
                        PrimitiveCtorInfo::Str => {
                            smallvec![DeconstructedCtor::NonExhaustive]
                        }
                        PrimitiveCtorInfo::Char => smallvec![
                            // The valid Unicode Scalar Value ranges.
                            make_range('\u{0000}' as u128, '\u{D7FF}' as u128),
                            make_range('\u{E000}' as u128, '\u{10FFFF}' as u128),
                        ],
                        PrimitiveCtorInfo::Array(_) =>
                        // @@Todo: investigate what should happen here, we should probably use a
                        // fixed array here.
                        {
                            smallvec![DeconstructedCtor::Array(Array {
                                kind: ArrayKind::Var(0, 0)
                            })]
                        }
                    },
                }
            }
            Ty::TupleTy(..) => smallvec![DeconstructedCtor::Single],
            _ => smallvec![DeconstructedCtor::NonExhaustive],
        };

        // Now we have to allocate `all_ctors` into storage
        let all_ctors = all_ctors.into_iter().map(|ctor| self.ctor_store().create(ctor)).collect();

        SplitWildcard { matrix_ctors: Vec::new(), all_ctors }
    }

    /// Perform a split on a [SplitWildcard], take `all_ctors` on the
    /// current [SplitWildcard] and split them with the provided constructors.
    pub(super) fn split_wildcard(
        &self,
        ctx: PatCtx,
        ctor: &mut SplitWildcard,
        ctors: impl Iterator<Item = DeconstructedCtorId> + Clone,
    ) {
        // Since `all_ctors` never contains wildcards, this won't recurse further.
        ctor.all_ctors = ctor
            .all_ctors
            .iter()
            .flat_map(|ctor| self.split_ctor(ctx, *ctor, ctors.clone()))
            .collect();

        ctor.matrix_ctors =
            ctors.filter(|c| !self.ctor_store().map_fast(*c, |c| c.is_wildcard())).collect();
    }

    /// Whether there are any value constructors for this type that are not
    /// present in the matrix.
    fn any_missing(&self, wildcard: &SplitWildcard) -> bool {
        self.iter_missing_ctors(wildcard).next().is_some()
    }

    /// Iterate over the constructors for this type that are not present in the
    /// matrix.
    pub(super) fn iter_missing_ctors<'a>(
        &'a self,
        wildcard: &'a SplitWildcard,
    ) -> impl Iterator<Item = DeconstructedCtorId> + 'a {
        wildcard
            .all_ctors
            .iter()
            .copied()
            .filter(move |ctor| !self.is_ctor_covered_by_any(*ctor, &wildcard.matrix_ctors))
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
    ) -> SmallVec<[DeconstructedCtorId; 1]> {
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
                || (ctx.is_top_level && try_use_ty_as_int_ty(ctx.ty).is_none())
            {
                DeconstructedCtor::Missing
            } else {
                DeconstructedCtor::Wildcard
            };

            let ctor = self.ctor_store().create(ctor);
            return smallvec![ctor];
        }

        wildcard.all_ctors
    }
}
