use smallvec::{smallvec, SmallVec};

use crate::{
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, Level1Term, NominalDef, Term},
        AccessToStorage, StorageRef,
    },
};

/// A wildcard constructor that we split relative to the constructors in the
/// matrix.
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

use super::{construct::Constructor, AccessToUsefulnessOps};

pub struct SplitWildcardOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for SplitWildcardOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> SplitWildcardOps<'gs, 'ls, 'cd, 's> {
    /// Create a new [SplitWildcardOps].
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Create a [SplitWildcard] from the current context.
    pub(super) fn from(&mut self, ctx: PatCtx) -> SplitWildcard {
        let reader = self.reader();

        // This determines the set of all possible constructors for the type `ctx.ty`.
        // For numbers, lists we use ranges and variable-length lists when appropriate.
        //
        //
        // @@Future:
        // we need make sure to omit constructors that are statically impossible. E.g.,
        // for `Option<!>`, we do not include `Some(_)` in the returned list of
        // constructors.
        let all_ctors = match reader.get_term(ctx.ty) {
            // term if ctx.typer().term_is_char() => ...,
            // term if ctx.typer().term_is_uint() => ...,
            // term if ctx.typer().term_is_int() => ...,
            // term if ctx.typer().term_is_list() => ...,
            Term::Level1(Level1Term::NominalDef(def)) => {
                match reader.get_nominal_def(*def) {
                    NominalDef::Struct(_) => smallvec![Constructor::Single],
                    NominalDef::Enum(enum_def) => {
                        // The exception is if the pattern is at the top level, because we
                        // want empty matches to be
                        // considered exhaustive.
                        let is_secretly_empty = enum_def.variants.is_empty() && !ctx.is_top_level;

                        let mut ctors: SmallVec<[_; 1]> = enum_def
                            .variants
                            .iter()
                            .enumerate()
                            .map(|(index, _)| Constructor::Variant(index))
                            .collect();

                        if is_secretly_empty {
                            ctors.push(Constructor::NonExhaustive);
                        }

                        ctors
                    }
                }
            }
            Term::Level1(Level1Term::Tuple(_)) => smallvec![Constructor::Single],
            _ => smallvec![Constructor::NonExhaustive],
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
    /// use the [Constructor::Missing] variant, otherwise falling back to
    /// [Constructor::Wildcard] in the situations where it is nonsensical
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
            let ctor = if !wildcard.matrix_ctors.is_empty() || (ctx.is_top_level)
            // @@TODO: and if it's not an integral
            {
                Constructor::Missing
            } else {
                Constructor::Wildcard
            };

            let ctor = self.constructor_store().create(ctor);
            return smallvec![ctor];
        }

        wildcard.all_ctors
    }
}
