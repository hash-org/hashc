//! Hash Typechecker pattern exhaustiveness module. This module contains all
//! of the machinery that is responsible for validating the exhaustiveness and
//! usefulness of patterns.
//!
//! Usefulness and exhaustiveness are inherently linked concepts, and are
//! computed in at the same time. In terms of `usefulness` we compute that if a
//! specified pattern `p` is useful in regards to a row of patterns `v` which
//! precede `p`. In other words, will this pattern `p` be ever reached if the
//! patterns `v` are specified before it. Usefulness determines if certain
//! branches in a `match` statement or other constructs that utilise patterns
//! will ever be matched.
//!
//! Exhaustiveness is similar to usefulness, but addresses the question of will
//! the provided row of patterns `v` cover all variants of some subject type.
//! For example, in the `match` block:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(_) => print("there is a number");
//!     None => print("there is no number");
//! };
//! ```
//!
//! So in this example, for `x` which is of type `Option<i32>`, will the
//! patterns: [`Some(_)`, `None`] cover all cases of `Option<i32>`. In this
//! situation yes, because both variants and their inner constructors because of
//! the wildcard `_`. However, a case where this property does not hold can be
//! easily constructed:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(3) => print("The number is 3!");
//!     None => print("there is no number");
//! };
//! ```
//!
//! Well here, we can come up with cases which the pattern set does not cover,
//! for example `Some(4)`. Therefore, the exhaustiveness check will conclude
//! that the provided pattern vector is not exhaustive and misses some cases.
//!
//! The implementation of this algorithm is based on the research paper:
//! http://moscova.inria.fr/~maranget/papers/warn/warn.pdf, and is heavily
//! inspired by the Rust Compiler implementation:
//! <https://github.com/rust-lang/rust/tree/master/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs>

mod constant;
pub mod fields;
pub mod structures;
pub mod usefulness;

use std::iter::once;

use self::{
    constant::Constant,
    fields::Fields,
    structures::{
        Constructor, DeconstructedPat, IntRange, List, ListKind, PatCtx, RangeEnd, SplitIntRange,
        SplitVarList, SplitWildcard,
    },
    usefulness::{MatchArm, MatchArmKind, Matrix, PatStack, Usefulness, UsefulnessReport, Witness, Reachability},
};
use crate::{
    diagnostics::{error::TcResult, macros::tc_panic},
    ops::{reader, AccessToOps},
    storage::{
        primitives::{
            self, ConstructedTerm, ConstructorPat, DeconstructedPatId, Level0Term, Level1Term,
            ListPat, LitTerm, NominalDef, NominalDefId, PatArg, PatArgsId, StructFields, Term,
            TermId, TupleLit, TupleTy,
        },
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    location::{SourceLocation, Span},
    string::Str,
};
use hash_utils::stack::ensure_sufficient_stack;
use if_chain::if_chain;
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};

#[derive(Debug, Clone)]
pub struct FieldPat {
    /// Relative to the associated definition
    index: usize,
    /// Pattern associated with this field
    pat: Pat,
}

/// [PatKind] represents a lowered form of patterns from [primitives::Pat]. This
/// removes unnecessary information about the actual pattern which doesn't
/// affect exhaustiveness and usefulness checking.
///
/// @@Future: we might need to introduce a new variant `Binding` if we introduce
/// patterns that can bind a name to a sub-pattern (as in rust `p @ ...PAT...`)
#[derive(Debug, Clone)]
pub enum PatKind {
    /// Wildcard match `_`
    Wild,

    /// Used to represent a spread pattern. It is used to temporarily build
    /// a [PatKind::List], later is thrown away and converted into a
    /// [PatKind::Wild] to simplify exhaustiveness checking.
    Spread,

    // Used to represent a constant pattern range, for integers and floats.
    //
    // **Note** currently only used to represent groupings of constants, as
    // range patterns aren't implemented yet!
    // Range {
    //     lo: Constant,
    //     hi: Constant,
    //     end: RangeEnd,
    // },
    ///

    /// Some constant value like a `char`, `u32`, etc. Booleans don't appear
    /// here because they are internally represented as enumerations.
    Constant {
        value: Constant,
    },

    /// Interned string pattern
    Str {
        value: Str,
    },

    /// A variant within an enumeration, e.g. `Some(3)`
    Variant {
        /// The id of the nominal definition that represents the enumeration.
        ///
        /// @@TODO: Replace this with id of union of structs, when `enum`s are
        /// no longer represented within `NominalDefId`
        def: NominalDefId,
        /// The inner patterns of the variant
        pats: Vec<FieldPat>,
        /// Which variant this variant represents within the parent definition.
        index: usize,
    },

    /// Essentially [PatKind::Variant], but for nominal definitions that only
    /// have one possible definition such as a struct `Dog(name = "..", ..)
    /// or tuple `(..)`.
    Leaf {
        pats: Vec<FieldPat>,
    },

    /// List pattern, holds the patterns that go before and after an
    /// optional `spread` pattern that is represented as a `wildcard`
    /// pattern.
    ///
    /// If the spread appears at the start of the list, then `prefix`
    /// pats will be empty, and the same applies if it appears at the
    /// end for `suffix`.
    List {
        // Patterns that precede an optional `...` spread selection
        prefix: Vec<Pat>,
        // The optional `...` spread
        spread: Option<Pat>,
        // Patterns that succeed an optional `...` spread selection
        suffix: Vec<Pat>,
    },

    // An `or` pattern, containing inner patterns that the `or` is applied onto.
    Or {
        pats: Vec<Pat>,
    },
}

/// General representation of a lowered pattern ready for exhaustiveness
/// analysis.
#[derive(Debug, Clone)]
pub struct Pat {
    /// Associated pattern span
    pub span: Span,
    /// The kind of the pattern
    pub kind: Box<PatKind>,
    /// If the pattern has an associated if-guard condition.
    pub has_guard: bool,
}

/// Contains functionality for converting patterns to a representation that
/// is suitable for performing usefulness and exhaustiveness analysis.
pub struct PatLowerCtx<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for PatLowerCtx<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> crate::storage::AccessToStorageMut for PatLowerCtx<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> PatLowerCtx<'gs, 'ls, 'cd, 's> {
    /// Create a new [PatCtx].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    pub fn location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, source_id: self.local_storage().current_source() }
    }

    /// Take a [primitives::Pat] and convert it into [Pat], essentially lowering
    /// the pattern.
    pub fn lower_pat(&mut self, id: primitives::PatId) -> TcResult<Pat> {
        let reader = self.reader();

        let pat = reader.get_pat(id);
        let span = self.location_store().get_span(id).unwrap();

        // Convert the pattern into a kind
        let kind = match pat {
            primitives::Pat::Binding(_)
            | primitives::Pat::Access(_)
            | primitives::Pat::Const(_)
            | primitives::Pat::Ignore
            | primitives::Pat::Mod(_) => PatKind::Wild,
            primitives::Pat::Spread(_) => PatKind::Spread,
            primitives::Pat::Lit(term) => return self.lower_constant(id, *term, span),
            // Tuple patterns are represented as leaves since they can't have alternative
            // variants
            primitives::Pat::Tuple(fields) => {
                let pats = self.lower_pat_fields(*fields)?;
                PatKind::Leaf { pats }
            }
            primitives::Pat::Constructor(_) => {
                return self.lower_constructor(pat.clone(), span);
            }
            primitives::Pat::List(ListPat { inner, .. }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];
                let mut spread = None;

                let pats = reader.get_pat_args(*inner).clone();

                // We don't care about the `name` of the arg because the list
                // never has the `name` assigned to anything...
                for PatArg { pat, .. } in pats.positional() {
                    let mut lowered_pat = self.lower_pat(*pat)?;

                    if matches!(lowered_pat.kind.as_ref(), PatKind::Spread) {
                        if spread.is_some() {
                            tc_panic!(pat, self, "found multiple spread patterns within list");
                        }

                        // Overwrite the kind into `Wild` to simplify things
                        let _ = std::mem::replace(&mut *lowered_pat.kind, PatKind::Wild);
                        spread = Some(lowered_pat);
                    } else {
                        match spread {
                            Some(_) => suffix.push(lowered_pat),
                            None => prefix.push(lowered_pat),
                        }
                    }
                }

                PatKind::List { prefix, spread, suffix }
            }
            primitives::Pat::Or(pats) => PatKind::Or {
                pats: pats.clone().into_iter().flat_map(|pat| self.lower_pat(pat)).collect_vec(),
            },
            primitives::Pat::If(if_pat) => {
                // we need to set `has_guard` to true on the pattern
                let mut inner = self.lower_pat(if_pat.pat)?;
                inner.has_guard = true;

                return Ok(inner);
            }
        };

        Ok(Pat { span, kind: Box::new(kind), has_guard: false })
    }

    /// Function to lower a [primitives::Pat::Constructor]. If the constructor
    /// subject is an enum variant, it will create a [PatKind::Variant]
    /// pattern, otherwise it uses [PatKind::Leaf] to represent other
    /// definitions.
    ///
    /// **Note** the term of the subject of the constructor must be simplified!
    pub fn lower_constructor(&mut self, pat: primitives::Pat, span: Span) -> TcResult<Pat> {
        let ConstructorPat { subject, args } = match pat {
            primitives::Pat::Constructor(constructor) => constructor,
            _ => unreachable!(),
        };

        // Transform the arguments into fields, since it doesn't matter
        // whether this will become a variant or a leaf.
        let pats = self.lower_pat_fields(args)?;

        // We need to determine if this is a enumeration or a struct, if it is a
        // struct, we can easily conclude that this lowered pattern is a `Leaf`,
        // otherwise it becomes a variant kind
        let reader = self.reader();
        let term = reader.get_term(subject);

        let kind = match term {
            primitives::Term::Level1(Level1Term::NominalDef(id)) => {
                let nominal_def = reader.get_nominal_def(*id);

                match nominal_def {
                    NominalDef::Struct(_) => PatKind::Leaf { pats },
                    // @@Todo: get the variant index here
                    NominalDef::Enum(_) => PatKind::Variant { def: *id, pats, index: 0 },
                }
            }
            // Was the subject not simplified :^( ?
            _ => tc_panic!(subject, self, "Not a nominal!"),
        };

        Ok(Pat { kind: Box::new(kind), span, has_guard: false })
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    pub fn lower_pat_fields(&mut self, fields: PatArgsId) -> TcResult<Vec<FieldPat>> {
        let reader = self.reader();
        let args = reader.get_pat_args(fields).clone();

        let pats = args
            .positional()
            .iter()
            .enumerate()
            // This tries to resolve the `index` of the argument that is being passed
            // within the tuple field. If the tuple has named arguments, then we have
            // to use the parameter list in order to resolve the index. By now it should be
            // verified that no un-named arguments appear after named arguments as this
            // creates an ambiguous ordering of arguments.
            .flat_map(|(index, arg)| -> TcResult<FieldPat> {
                let field = if_chain! {
                    if let Some(name) = arg.name;
                    if let Some((arg_index, _)) = args.get_by_name(name);
                    then {
                        arg_index
                    } else {
                        index
                    }
                };

                Ok(FieldPat { index: field, pat: self.lower_pat(arg.pat)? })
            })
            .collect_vec();

        Ok(pats)
    }

    /// Function that performs a lowering operation on a [Level0Term::Lit] and
    /// converts it into a [PatKind::Constant] or a [PatKind::Str] if it is
    /// a string.
    pub fn lower_constant(
        &mut self,
        pat: primitives::PatId,
        ty: TermId,
        span: Span,
    ) -> TcResult<Pat> {
        let reader = self.reader();
        let value = reader.get_term(ty);

        let kind = match value {
            primitives::Term::Level0(Level0Term::Lit(lit)) => match lit {
                primitives::LitTerm::Str(value) => PatKind::Str { value: *value },
                primitives::LitTerm::Int { value, kind } => {
                    PatKind::Constant { value: Constant::from_int(value.clone(), *kind, ty) }
                }
                primitives::LitTerm::Char(value) => {
                    PatKind::Constant { value: Constant::from_char(*value, ty) }
                }
            },
            _ => tc_panic!(pat, self, "Not a constant!"),
        };

        Ok(Pat { kind: Box::new(kind), span, has_guard: false })
    }

    /// Compute the `arity` of this [Constructor].
    pub(crate) fn ctor_arity(&self, ctx: PatCtx, ctor: &Constructor) -> usize {
        match ctor {
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
                            NominalDef::Enum(_) => todo!(),
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
    /// know will behave the same wrt the current matrix, we keep them
    /// grouped. For example, all lists of a sufficiently large length will
    /// either be all useful or all non-useful with a given matrix.
    ///
    /// See the branches for details on how the splitting is done.
    ///
    /// ## Discarding constructors
    ///
    /// This function may discard some irrelevant constructors if this preserves
    /// behaviour and diagnostics. For example, for the `_` case, we ignore the
    /// constructors already present in the matrix, unless all of them are.
    pub(super) fn split_ctor<'a>(
        &self,
        ctx: PatCtx,
        ctor: &Constructor,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) -> SmallVec<[Constructor; 1]> {
        match ctor {
            Constructor::Wildcard => {
                let mut wildcard = self.split_wildcard_from(ctx);
                self.split_wildcard(ctx, &mut wildcard, ctors);
                self.split_wildcard_into_ctors(ctx, wildcard)
            }
            // Fast track to just the single constructor if this range is trivial
            Constructor::IntRange(range) if !range.is_singleton() => {
                let mut split_range = SplitIntRange::new(range.clone());
                let int_ranges = ctors.filter_map(|ctor| ctor.as_int_range());

                split_range.split(int_ranges.cloned());
                split_range.iter().map(Constructor::IntRange).collect()
            }
            &Constructor::List(List { kind: ListKind::Var(prefix_len, suffix_len) }) => {
                let mut split_self = SplitVarList::new(prefix_len, suffix_len);

                let slices = ctors.filter_map(|c| c.as_list()).map(|s| s.kind);
                split_self.split(slices);
                split_self.iter().map(Constructor::List).collect()
            }
            // In any other case, the split just puts this constructor
            // into the
            _ => smallvec![ctor.clone()],
        }
    }

    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a
    /// subset of `other`. For the simple cases, this is simply checking for
    /// equality. For the "grouped" constructors, this checks for inclusion.
    #[inline]
    pub(super) fn is_covered_by(
        &self,
        ctx: PatCtx,
        ctor: &Constructor,
        other: &Constructor,
    ) -> bool {
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
    fn ctor_covered_by_any(
        &self,
        ctx: PatCtx,
        ctor: &Constructor,
        used_ctors: &[Constructor],
    ) -> bool {
        if used_ctors.is_empty() {
            return false;
        }

        match ctor {
            // If `self` is `Single`, `used_ctors` cannot contain anything else than `Single`s.
            Constructor::Single => !used_ctors.is_empty(),
            Constructor::Variant(i) => {
                used_ctors.iter().any(|c| matches!(c, Constructor::Variant(k) if k == i))
            }
            Constructor::IntRange(range) => used_ctors
                .iter()
                .filter_map(|c| c.as_int_range())
                .any(|other| range.is_covered_by(other)),
            Constructor::List(list) => used_ctors
                .iter()
                .filter_map(|c| c.as_list())
                .any(|other| list.is_covered_by(*other)),
            // This constructor is never covered by anything else
            Constructor::NonExhaustive => false,
            Constructor::Str(_)
            | Constructor::Missing
            | Constructor::Wildcard
            | Constructor::Or => {
                panic_on_span!(
                    self.location(ctx.span),
                    self.source_map(),
                    "Unexpected ctor in all_ctors"
                )
            }
        }
    }

    pub(super) fn split_wildcard_from(&self, ctx: PatCtx) -> SplitWildcard {
        let reader = self.reader();

        // let make_range = |ctx, start, end| {
        //     Constructor::IntRange(IntRange::from_range(ctx, start, end,
        // &RangeEnd::Included)) };

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

        SplitWildcard { matrix_ctors: Vec::new(), all_ctors }
    }

    pub(super) fn split_wildcard<'a>(
        &self,
        ctx: PatCtx,
        ctor: &mut SplitWildcard,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) {
        // Since `all_ctors` never contains wildcards, this won't recurse further.
        ctor.all_ctors = ctor
            .all_ctors
            .iter()
            .flat_map(|ctor| self.split_ctor(ctx, ctor, ctors.clone()))
            .collect();
        ctor.matrix_ctors = ctors.filter(|c| !c.is_wildcard()).cloned().collect();
    }

    /// Whether there are any value constructors for this type that are not
    /// present in the matrix.
    fn any_missing_from_wildcard(&self, ctx: PatCtx, ctor: &SplitWildcard) -> bool {
        self.wildcard_iter_missing(ctx, ctor).next().is_some()
    }

    /// Iterate over the constructors for this type that are not present in the
    /// matrix.
    pub(super) fn wildcard_iter_missing<'a>(
        &self,
        ctx: PatCtx,
        wildcard: &'a SplitWildcard,
    ) -> impl Iterator<Item = &'a Constructor> {
        // Sigh

        wildcard.all_ctors.iter()
        // .filter(move |ctor| !self.ctor_covered_by_any(ctx, ctor,
        // &wildcard.matrix_ctors))
    }

    fn split_wildcard_into_ctors(
        &self,
        ctx: PatCtx,
        wildcard: SplitWildcard,
    ) -> SmallVec<[Constructor; 1]> {
        // If Some constructors are missing, thus we can specialize with the special
        // `Missing` constructor, which stands for those constructors that are
        // not seen in the matrix, and matches the same rows as any of them
        // (namely the wildcard rows). See the top of the file for details.
        if self.any_missing_from_wildcard(ctx, &wildcard) {
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

            return smallvec![ctor];
        }

        wildcard.all_ctors
    }

    /// Attempt to build a [IntRange] from a provided constant.
    #[inline]
    pub fn int_range_from_constant(&self, constant: Constant) -> IntRange {
        let reader = self.reader();

        let bias: u128 = match reader.get_term(constant.ty) {
            Term::Level0(Level0Term::Lit(lit)) => match lit {
                LitTerm::Int { kind, .. } if kind.is_signed() => {
                    // @@Todo: support `ibig` type here
                    let size = kind.size().unwrap();
                    1u128 << (size * 8 - 1)
                }
                LitTerm::Char(_) | LitTerm::Int { .. } => 0,
                LitTerm::Str(_) => panic!("got `str` in const!"),
            },
            _ => tc_panic!(
                constant.ty,
                self,
                "got unexpected ty `{}` when reading Constant.",
                self.for_fmt(constant.ty)
            ),
        };

        // read from the constant the actual bits and apply bias
        let val = constant.data() ^ bias;
        IntRange { range: val..=val, bias }
    }

    /// Create an [IntRange] from two specified bounds, and assuming that the
    /// type is an integer (of the column)
    fn int_range_from_range(&self, ctx: PatCtx, lo: u128, hi: u128, end: &RangeEnd) -> IntRange {
        let bias = self.int_range_signed_bias(ctx);

        let (lo, hi) = (lo ^ bias, hi ^ bias);
        let offset = (*end == RangeEnd::Excluded) as u128;
        if lo > hi || (lo == hi && *end == RangeEnd::Excluded) {
            panic!("malformed range pattern: {}..={}", lo, (hi - offset));
        }

        IntRange { range: lo..=(hi - offset), bias }
    }

    /// Get the bias based on the type, if it is a signed, integer then
    /// the bias is set to be just at the end of the signed boundary
    /// of the integer size, in other words at the position where the
    /// last byte is that identifies the sign.
    fn int_range_signed_bias(&self, ctx: PatCtx) -> u128 {
        let reader = self.reader();

        match reader.get_term(ctx.ty) {
            Term::Level0(Level0Term::Lit(LitTerm::Int { kind, .. })) if kind.is_signed() => {
                // @@Future: support `ibig` here
                let size = kind.size().unwrap();
                1u128 << (size * 8 - 1)
            }
            _ => 0,
        }
    }

    /// Convert this range into a [PatKind] by judging the given
    /// type within the [PatCtx]
    #[inline]
    pub fn int_range_to_pat(&self, range: &IntRange, ctx: PatCtx) -> PatKind {
        let (lo, hi) = range.boundaries();

        let bias = range.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        let lo_const = Constant::from_u128(lo, ctx.ty);
        // let hi_const = Constant::from_u128(hi, ctx.ty);

        if lo == hi {
            PatKind::Constant { value: lo_const }
        } else {
            panic!("Ranges are not supported yet")
        }
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn deconstructed_from_pat<'p>(
        &mut self,
        ctx: PatCtx,
        pat: &'p Pat,
    ) -> DeconstructedPat {
        // @@Todo: support int, and float ranges
        let (ctor, fields) = match pat.kind.as_ref() {
            PatKind::Spread | PatKind::Wild => (Constructor::Wildcard, vec![]),
            PatKind::Constant { value } => {
                // This deals with `char` and `integer` types...
                let range = self.int_range_from_constant(*value);
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
                            .map(|member| DeconstructedPat::wildcard(member.value))
                            .collect();

                        for field in pats {
                            wilds[field.index] = self.deconstructed_from_pat(ctx, &field.pat);
                        }

                        // let fields = Fields::from_iter(ctx, wilds);
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

                        let mut wilds: SmallVec<[_; 2]> =
                            tys.map(DeconstructedPat::wildcard).collect();

                        for field in pats {
                            wilds[field.index] = self.deconstructed_from_pat(ctx, &field.pat);
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
                let fields = prefix
                    .iter()
                    .chain(suffix)
                    .map(|pat| self.deconstructed_from_pat(ctx, pat))
                    .collect_vec();

                (ctor, fields)
            }
            PatKind::Or { .. } => {
                // here, we need to expand the or pattern, so that all of the
                // children patterns of the `or` become fields of the
                // deconstructed  pat.
                let pats = DeconstructedPat::flatten_or_pat(pat);

                let fields =
                    pats.iter().map(|pat| self.deconstructed_from_pat(ctx, pat)).collect_vec();

                (Constructor::Or, fields)
            }
        };

        // Now we need to put them in the slotmap...
        let fields = Fields::from_iter(
            fields.into_iter().map(|field| self.deconstructed_pat_store_mut().create(field)),
        );

        DeconstructedPat::new(ctor, fields, ctx.ty, pat.span)
    }

    pub(crate) fn deconstructed_to_pat(&self, ctx: PatCtx, pat: DeconstructedPatId) -> Pat {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat_fields(pat);

        let children =
            pat.fields.iter_patterns().map(|p| self.deconstructed_to_pat(ctx, *p)).collect_vec();

        let kind = match &pat.ctor {
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

                                        PatKind::Variant { def: *id, pats, index: *index }
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
            Constructor::IntRange(range) => self.int_range_to_pat(range, ctx),
            Constructor::Str(value) => PatKind::Str { value: *value },
            Constructor::List(List { kind }) => match kind {
                ListKind::Fixed(_) => {
                    PatKind::List { prefix: children, spread: None, suffix: vec![] }
                }
                ListKind::Var(prefix, _) => {
                    let mut children = children.into_iter().peekable();

                    // build the prefix and suffix components
                    let prefix: Vec<_> = children.by_ref().take(*prefix).collect();
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
        &self,
        ctx: PatCtx,
        pat: DeconstructedPatId,
        other_ctor: &Constructor,
    ) -> SmallVec<[DeconstructedPatId; 2]> {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat_fields(pat);

        match (&pat.ctor, other_ctor) {
            (Constructor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                self.fields_wildcards(ctx, other_ctor).iter_patterns().copied().collect()
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
                    ListKind::Var(prefix, suffix) => {
                        // @@Todo: we will need to get the inner `ty` of the list

                        let prefix = &pat.fields.fields[..prefix];
                        let suffix = &pat.fields.fields[self_list.arity() - suffix..];

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

    /// Creates a new list of wildcard fields for a given constructor. The
    /// result must have a length of `ctor.arity()`.
    pub(super) fn fields_wildcards(&self, ctx: PatCtx, ctor: &Constructor) -> Fields {
        match ctor {
            Constructor::Single | Constructor::Variant(_) => {
                let reader = self.reader();

                match reader.get_term(ctx.ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        let members = reader.get_params(*members);
                        let tys = members.positional().iter().map(|member| member.ty).collect_vec();

                        Fields::wildcards_from_tys(tys)
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

                                    Fields::wildcards_from_tys(tys)
                                }
                                StructFields::Opaque => tc_panic!(
                                    ctx.ty,
                                    self,
                                    "Unexpected ty `{}` when getting wildcards in Fields::wildcards",
                                    self.for_fmt(ctx.ty),
                                ),
                            },
                            // @@Remove: when enums aren't represented as this anymore
                            NominalDef::Enum(_) => todo!(),
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
                let ty = todo!();

                Fields::wildcards_from_tys((0..arity).map(|_| ty))
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

    // /// Report the spans of sub-patterns that were not reachable, if any.
    pub(super) fn unreachable_spans(&self, pat: &DeconstructedPat) -> Vec<Span> {
        let mut spans = Vec::new();
        self.collect_unreachable_spans(pat, &mut spans);
        spans
    }

    fn collect_unreachable_spans(&self, pat: &DeconstructedPat, spans: &mut Vec<Span>) {
        // We don't look at sub-patterns if we
        // already reported the whole pattern as  unreachable.
        if !pat.is_reachable() {
            spans.push(pat.span);
        } else {
            let reader = self.reader();

            for p in pat.fields.iter_patterns() {
                let p = reader.get_deconstructed_pat_fields(*p);
                self.collect_unreachable_spans(p, spans);
            }
        }
    }

    /// Constructs a partial witness for a pattern given a list of
    /// patterns expanded by the specialization step.
    ///
    /// When a pattern P is discovered to be useful, this function is used
    /// bottom-up to reconstruct a complete witness, e.g., a pattern P' that    
    /// covers a subset of values, V, where each value in that set is not
    /// covered by any previously used patterns and is covered by the
    /// pattern P'. Examples:
    ///
    /// left_ty: tuple of 3 elements
    /// pats: [10, 20, _]           => (10, 20, _)
    ///
    /// left_ty: struct X { a: (bool, &'static str), b: usize}
    /// pats: [(false, "foo"), 42]  => X { a: (false, "foo"), b: 42 }
    fn witness_apply_constructor(
        &mut self,
        ctx: PatCtx,
        mut witness: Witness,
        ctor: &Constructor,
    ) -> Witness {
        let pat = {
            let len = witness.0.len();
            let arity = self.ctor_arity(ctx, ctor);

            let pats = witness.0.drain((len - arity)..).rev();
            let fields = Fields::from_iter(pats);

            DeconstructedPat::new(ctor.clone(), fields, ctx.ty, Span::dummy())
        };

        let pat = self.deconstructed_pat_store_mut().create(pat);
        witness.0.push(pat);
        witness
    }

    /// Recursively expand the first pattern into its sub-patterns. Only useful
    /// if the pattern is an or-pattern.
    ///
    /// Panics if `self` is empty.
    fn pat_stack_expand_or_pat(&self, stack: &PatStack) -> Vec<PatStack> {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat_fields(stack.head());

        pat.fields
            .clone()
            .iter_patterns()
            .map(move |pat| {
                let mut new_stack = PatStack::singleton(*pat);

                new_stack.pats.extend_from_slice(&stack.pats[1..]);
                new_stack
            })
            .collect()
    }

    /// This computes `S(self.head().ctor(), self)`. See top of the file for
    /// explanations.
    ///
    ///
    /// @@Todo: Structure patterns with a partial wild pattern `Foo(a: 42,..)`
    /// have their missing fields filled with wild patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    fn pat_stack_pop_head_constructor(
        &self,
        ctx: PatCtx,
        stack: &PatStack,
        ctor: &Constructor,
    ) -> PatStack {
        // We pop the head pattern and push the new fields extracted from the arguments
        // of `self.head()`.
        let mut new_fields: SmallVec<[_; 2]> = self.specialise(ctx, stack.head(), ctor);
        new_fields.extend_from_slice(&stack.pats[1..]);

        PatStack::from_vec(new_fields)
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern,
    /// this recursively expands it.
    fn matrix_push(&self, matrix: &mut Matrix, row: PatStack) {
        let reader = self.reader();
        let ctor = reader.get_deconstructed_pat_fields(row.head());

        if !row.is_empty() && ctor.is_or_pat() {
            matrix.patterns.extend(self.pat_stack_expand_or_pat(&row));
        } else {
            matrix.patterns.push(row);
        }
    }

    /// This computes `S(constructor, self)`. See top of the file for
    /// explanations.
    fn matrix_specialize_constructor(
        &self,
        ctx: PatCtx,
        matrix: &Matrix,
        ctor: &Constructor,
    ) -> Matrix {
        let reader = self.reader();
        let mut s_matrix = Matrix::empty();

        for row in &matrix.patterns {
            let head = reader.get_deconstructed_pat_fields(row.head());
            if self.is_covered_by(ctx, ctor, head.ctor()) {
                let new_row = self.pat_stack_pop_head_constructor(ctx, row, ctor);
                self.matrix_push(&mut s_matrix, new_row);
            }
        }
        s_matrix
    }

    pub(super) fn wild_from_ctor(&self, ctx: PatCtx, ctor: Constructor) -> DeconstructedPat {
        let fields = self.fields_wildcards(ctx, &ctor);

        DeconstructedPat::new(ctor, fields, ctx.ty, Span::dummy())
    }

    /// After calculating usefulness after a specialization, call this to
    /// reconstruct a usefulness that makes sense for the matrix
    /// pre-specialization. This new usefulness can then be merged
    /// with the results of specializing with the other constructors.
    fn usefulness_apply_constructor(
        &mut self,
        ctx: PatCtx,
        usefulness: Usefulness,
        matrix: &Matrix, // used to compute missing ctors
        ctor: &Constructor,
    ) -> Usefulness {
        match usefulness {
            Usefulness::NoWitnesses { .. } => usefulness,
            Usefulness::WithWitnesses(ref witnesses) if witnesses.is_empty() => usefulness,
            Usefulness::WithWitnesses(witnesses) => {
                let new_witnesses = if let Constructor::Missing = ctor {
                    let reader = self.reader();

                    // We got the special `Missing` constructor, so each of the missing constructors
                    // gives a new  pattern that is not caught by the match. We
                    // list those patterns.
                    let mut wildcard = self.split_wildcard_from(ctx);
                    self.split_wildcard(
                        ctx,
                        &mut wildcard,
                        matrix.heads().map(|id| reader.get_deconstructed_pat_fields(id).ctor()),
                    );

                    // Get all the missing constructors for the current type
                    let missing_ctors = self.wildcard_iter_missing(ctx, &wildcard);

                    let new_pats = missing_ctors
                        .into_iter()
                        .map(|missing_ctor| {
                            let pat = self.wild_from_ctor(ctx, missing_ctor.clone());
                            self.deconstructed_pat_store_mut().create(pat)
                        })
                        .collect_vec();

                    // Firstly, read all of the patterns stored in the current witness
                    // and clone them whilst forgetting
                    // the reachability
                    let t: Vec<_> = witnesses
                        .into_iter()
                        .flat_map(|witness| {
                            new_pats.iter().map(move |pat| {
                                witness.0.clone().iter().copied().chain(once(*pat)).collect_vec()
                            })
                        })
                        .collect();

                    let mut new_witnesses = vec![];

                    for inner in t {
                        let mut new_inner = vec![];

                        for pat in inner {
                            let reader = self.reader();

                            let new_pat = reader
                                .get_deconstructed_pat_fields(pat)
                                .clone_and_forget_reachability();

                            let new_pat = self.deconstructed_pat_store_mut().create(new_pat);
                            new_inner.push(new_pat);
                        }

                        new_witnesses.push(Witness(new_inner))
                    }

                    new_witnesses
                } else {
                    witnesses
                        .into_iter()
                        .map(|witness| self.witness_apply_constructor(ctx, witness, ctor))
                        .collect()
                };

                Usefulness::WithWitnesses(new_witnesses)
            }
        }
    }

    /// Algorithm from <http://moscova.inria.fr/~maranget/papers/warn/index.html>.
    /// The algorithm from the paper has been modified to correctly handle empty
    /// types. The changes are:
    ///   (0) We don't exit early if the pattern matrix has zero rows. We just
    ///       continue to recurse over columns.
    ///   (1) all_constructors will only return constructors that are statically
    ///       possible. E.g., it will only return `Ok` for `Result<T, !>`.
    ///
    /// This finds whether a (row) vector `v` of patterns is 'useful' in
    /// relation to a set of such vectors `m` - this is defined as there
    /// being a set of inputs that will match `v` but not any of the sets in
    /// `m`.
    ///
    /// All the patterns at each column of the `matrix ++ v` matrix must have
    /// the same type.
    ///
    /// This is used both for reachability checking (if a pattern isn't useful
    /// in relation to preceding patterns, it is not reachable) and
    /// exhaustiveness checking (if a wildcard pattern is useful in relation
    /// to a matrix, the matrix isn't exhaustive).
    ///
    /// `is_under_guard` is used to inform if the pattern has a guard. If it
    /// has one it must not be inserted into the matrix. This shouldn't be
    /// relied on for soundness.
    fn is_useful(
        &mut self,
        matrix: &Matrix,
        v: &PatStack,
        arm_kind: MatchArmKind,
        is_under_guard: bool,
        is_top_level: bool,
    ) -> Usefulness {
        let Matrix { patterns: rows, .. } = matrix;

        // The base case. We are pattern-matching on () and the return value is
        // based on whether our matrix has a row or not.
        if v.is_empty() {
            let ret = if rows.is_empty() {
                Usefulness::new_useful(arm_kind)
            } else {
                Usefulness::new_not_useful(arm_kind)
            };

            return ret;
        }

        let reader = self.reader();
        let head = reader.get_deconstructed_pat_fields(v.head());

        let ty = head.ty();
        let span = head.span();

        // Create a new `PatCtx`, based on on the provided parameters
        let ctx = PatCtx::new(ty, span, is_top_level);
        let mut report = Usefulness::new_not_useful(arm_kind);

        // If the first pattern is an or-pattern, expand it.
        if head.is_or_pat() {
            // We try each or-pattern branch in turn.
            let mut matrix = matrix.clone();

            for v in self.pat_stack_expand_or_pat(v) {
                let usefulness = ensure_sufficient_stack(|| {
                    self.is_useful(&matrix, &v, arm_kind, is_under_guard, false)
                });

                report.extend(usefulness);

                // @@Todo: deal with `if-guards` on the patterns themselves.
                //
                // If the pattern has a guard don't add it to the matrix, but otherwise
                // just push it into the matrix, it doesn't matter if it has already
                //  been seen in the current `or` pattern since we want to detect redundant
                // members within the or pattern as well... for example:
                // ``` Ok(_) | Ok(3) => ...; ```
                //
                if !is_under_guard {
                    self.matrix_push(&mut matrix, v);
                }
            }
        } else {
            let v_ctor = head.ctor();

            // @@Todo: we should check that int ranges don't overlap here, in case
            // they're partially covered by other ranges.

            let ctors = matrix.heads().map(|id| reader.get_deconstructed_pat_fields(id).ctor());

            // We split the head constructor of `v`.
            let split_ctors = self.split_ctor(ctx, v_ctor, ctors);
            let start_matrix = &matrix;

            // For each constructor, we compute whether there's a value that starts with it
            // that would witness the usefulness of `v`.
            for ctor in split_ctors {
                // cache the result of `Fields::wildcards` because it is used a lot.
                let spec_matrix = self.matrix_specialize_constructor(ctx, start_matrix, &ctor);
                let v = self.pat_stack_pop_head_constructor(ctx, v, &ctor);

                let usefulness = ensure_sufficient_stack(|| {
                    self.is_useful(&spec_matrix, &v, arm_kind, is_under_guard, false)
                });

                let usefulness =
                    self.usefulness_apply_constructor(ctx, usefulness, start_matrix, &ctor);
                report.extend(usefulness);
            }
        }

        if report.is_useful() {
            let head = self.deconstructed_pat_store_mut().get_mut(v.head());
            head.set_reachable();
        }

        report
    }

    pub(crate) fn compute_match_usefulness(
        &mut self,
        _subject: TermId,
        arms: &[MatchArm],
    ) -> UsefulnessReport {
        let mut matrix = Matrix::empty();

        // Compute usefulness for each arm in the match
        let arm_usefulness: Vec<_> = arms
            .iter()
            .copied()
            .map(|arm| {
                let v = PatStack::singleton(arm.pat);
                self.is_useful(
                    &matrix,
                    &v,
                    MatchArmKind::Real,
                    arm.has_guard,
                    true,
                );

                // We still compute the usefulness of if-guard patterns, but we don't
                // add them into the matrix since we can't guarantee that they
                // yield all possible conditions
                if !arm.has_guard {
                    self.matrix_push(&mut matrix, v);
                }

                let reader = self.reader();
                let pat = reader.get_deconstructed_pat_fields(arm.pat);

                let reachability = if pat.is_reachable() {
                    Reachability::Reachable(self.unreachable_spans(pat))
                } else {
                    Reachability::Unreachable
                };
                (arm, reachability)
            })
            .collect();

        // @@Todo: create the wildcard, using an arena
        // let wildcard = ...;
        // let v = PatStack::singleton(v);

        let v = PatStack::from_vec(smallvec![]);

        let usefulness = self.is_useful(
            &matrix,
            &v,
            MatchArmKind::ExhaustiveWildcard,
            false,
            true,
        );

        // It should not be possible to not get any witnesses since we're matching
        // on a wildcard, the base case is that `pats` is empty and thus the
        // set of patterns that are provided in the match block are exhaustive.
        let non_exhaustiveness_witnesses = match usefulness {
            Usefulness::WithWitnesses(pats) => {
                pats.into_iter().map(|w| w.single_pattern()).collect()
            }
            Usefulness::NoWitnesses { .. } => panic!(),
        };

        UsefulnessReport { arm_usefulness, non_exhaustiveness_witnesses }
    }
}
