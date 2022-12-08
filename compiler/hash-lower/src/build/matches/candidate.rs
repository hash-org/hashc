//! Definitions for [Candidate]s that are used to represent
//! arms within a `match` block, specifically when code is
//! being generated to efficiently group and select where
//! to jump to next.
//!
//! @@Todo: This implementation is not fully complete and doesn't handle the
//!         full range of patterns (most of this will go away with the new
//! pattern         representation). Notably, the following problems persist:
//!
//! 1. `if-guards` that are located on sub-patterns are not properly
//! handled, it is assumed there is an outermost 'if-guard' that is
//! used to determine the control flow, amongst other things.
//!
//! 2. spread patterns (`...`) are not properly handled because they
//! aren't associated with a particular parent pattern, which makes it
//! hard to reason about them. When we switch to the new pattern
//! representation, it will be significantly easier to deal with `...`
//! patterns (specifically, when they are binding).

use std::{borrow::Borrow, mem};

use hash_ast::ast::{AstNodeRef, MatchCase, RangeEnd};
use hash_ir::{
    ir::{BasicBlock, Place, PlaceProjection},
    ty::{AdtId, IrTy, Mutability},
};
use hash_source::{constant::CONSTANT_MAP, identifier::Identifier, location::Span};
use hash_target::size::Size;
use hash_types::{
    pats::{
        BindingPat, ConstructorPat, IfPat, ListPat, Pat, PatArgsId, PatId, RangePat, SpreadPat,
    },
    terms::{Level0Term, LitTerm, Term, TermId},
};
use hash_utils::store::Store;
use smallvec::{smallvec, SmallVec};

use crate::build::{place::PlaceBuilder, Builder};

pub(super) struct Candidate {
    /// The span of the `match` arm, for-error reporting
    /// functionality.
    pub span: Span,

    /// Whether or not the candidate arm hsa an associated guard,
    pub has_guard: bool,

    /// All the bindings that are created in the candidate arm.
    pub bindings: Vec<Binding>,

    /// The match pair that is associated with the binding.
    pub pairs: SmallVec<[MatchPair; 1]>,

    /// Block before all of the bindings have been established within
    /// the arm.
    pub pre_binding_block: Option<BasicBlock>,

    /// In the event that the guard is evaluated, this is the block that
    /// is jumped to if the guard is false.
    pub otherwise_block: Option<BasicBlock>,

    /// The `pre_binding_block` of the next candidate arm.
    pub next_candidate_pre_bind_block: Option<BasicBlock>,

    /// Any sub-candidates that are associated with this candidate.
    pub sub_candidates: Vec<Candidate>,
}

/// A [MatchPair] associates a pattern with a particular [Place] that
/// is used to access the underlying data when generating code for
/// comparing values of each [Candidate].
#[derive(Clone, Debug)]
pub(super) struct MatchPair {
    /// The ID of the pattern that occurs within a [Candidate].
    pub pat: PatId,

    /// The [Place] associated with this pattern. We use
    /// a [PlaceBuilder] since we might modify the place based on
    /// if we are performing various down-casts, field accesses on the
    /// way. We always start with the [Place] of the `match` subject, and
    /// build up each pattern place.
    pub place: PlaceBuilder,
}

pub(super) type Candidates<'tcx> = (AstNodeRef<'tcx, MatchCase>, Candidate);

impl Candidate {
    /// Create a new [Candidate].
    pub(super) fn new(span: Span, pat: PatId, place: &PlaceBuilder, has_guard: bool) -> Self {
        Self {
            span,
            has_guard,
            otherwise_block: None,
            pre_binding_block: None,
            next_candidate_pre_bind_block: None,
            // @@Todo: do we need to store an associated place with this pattern?
            pairs: smallvec![MatchPair { pat, place: place.clone() }],
            bindings: Vec::new(),
            sub_candidates: Vec::new(),
        }
    }

    /// Visit all of the leaves of a candidate and apply some operation on
    /// each one that is contained in the current candidate.
    pub(super) fn visit_leaves<'a>(&'a mut self, mut visit_leaf: impl FnMut(&'a mut Candidate)) {
        traverse_candidate(
            self,
            &mut (),
            &mut move |c, _| visit_leaf(c),
            move |c, _| c.sub_candidates.iter_mut(),
            |_| {},
        );
    }
}

/// A depth-first traversal of the [Candidate] and all of its recursive
/// sub candidates.
pub(super) fn traverse_candidate<C, T, I>(
    candidate: C,
    context: &mut T,
    visit_leaf: &mut impl FnMut(C, &mut T),
    get_children: impl Copy + Fn(C, &mut T) -> I,
    complete_children: impl Copy + Fn(&mut T),
) where
    C: Borrow<Candidate>,
    I: Iterator<Item = C>,
{
    if candidate.borrow().sub_candidates.is_empty() {
        visit_leaf(candidate, context);
    } else {
        for child in get_children(candidate, context) {
            traverse_candidate(child, context, visit_leaf, get_children, complete_children);
        }

        complete_children(context);
    }
}

/// All the bindings that occur in a `match` arm.
#[derive(Debug, Clone)]
pub(super) struct Binding {
    /// The span of the binding.
    pub span: Span,

    /// The source of the binding, where the value is coming from.
    pub source: Place,

    /// The identifier that is used as the binding.
    pub name: Identifier,

    /// The mutability of the binding
    pub mutability: Mutability,

    /// The mode of the bind, whether it is by reference or by the value.
    pub mode: BindingMode,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum BindingMode {
    ByValue,
    ByRef,
}

impl<'tcx> Builder<'tcx> {
    /// This function attempts to simplify a [Candidate] so that all match pairs
    /// can be tested. This method will also split the candidate in which
    /// the only match pair is a `or` pattern, in order for matches like:
    /// ```ignore
    /// match x {
    ///    1 | 2 => {}
    ///    4 | 6 => {}
    /// }
    /// ```
    /// Will generate a single switch table.
    ///
    /// The function returns a boolean denoting whether it has performed any
    /// splits on the given candidate.
    pub(super) fn simplify_candidate(&mut self, candidate: &mut Candidate) -> bool {
        // keep a record of the existing bindings and all of the bindings that
        // are to be added when exploring the pattern.
        let mut existing_bindings = mem::take(&mut candidate.bindings);
        let mut new_bindings = Vec::new();

        loop {
            let match_pairs = mem::take(&mut candidate.pairs);

            // Check if the bindings has a single or-pattern
            if let [pair] = &*match_pairs {
                if self.tcx.pat_store.map_fast(pair.pat, Pat::is_or) {
                    // append all the new bindings, and then swap the two vecs around
                    existing_bindings.extend_from_slice(&new_bindings);
                    mem::swap(&mut candidate.bindings, &mut existing_bindings);

                    // Now we need to create sub-candidates for each of the or-patterns
                    return self.tcx.pat_store.map_fast(pair.pat, |pat| {
                        let Pat::Or(sub_pats) = pat else {
                            unreachable!()
                        };

                        candidate.sub_candidates =
                            self.create_sub_candidates(&pair.place, candidate, sub_pats);

                        true
                    });
                }
            }

            // There are multiple patterns to check here, so we need to iterate
            // over each one and perform a simplification...
            let mut changed = false;

            for pair in match_pairs {
                match self.simplify_match_pair(pair, candidate) {
                    Ok(_) => {
                        changed = true;
                    }
                    // We need to re-evaluate one of the patterns later on
                    Err(pair) => candidate.pairs.push(pair),
                }
            }

            // Combine the `new` bindings with the ones in the candidate, then swap
            // the vectors, and delete the old candidate bindings.
            candidate.bindings.extend_from_slice(&new_bindings);
            mem::swap(&mut candidate.bindings, &mut new_bindings);
            candidate.bindings.clear();

            if !changed {
                // append all the new bindings, and then swap the two vecs around
                existing_bindings.extend_from_slice(&new_bindings);
                mem::swap(&mut candidate.bindings, &mut existing_bindings);

                // sort all of the pats in the candidate by `or-pat` last
                candidate
                    .pairs
                    .sort_by_key(|pair| self.tcx.pat_store.map_fast(pair.pat, Pat::is_or));

                // We weren't able to perform any further simplifications, so return false
                return false;
            }
        }
    }

    /// Tries to simplify `match_pair`, returning `Ok(())` if
    /// successful. If successful, new match pairs and bindings will
    /// have been pushed into the candidate. If no simplification is
    /// possible, `Err` is returned and no changes are made to
    /// candidate.
    pub(super) fn simplify_match_pair(
        &mut self,
        pair: MatchPair,
        candidate: &mut Candidate,
    ) -> Result<(), MatchPair> {
        self.tcx.pat_store.map_fast(pair.pat, |pat| {
            // Get the span of this particular pattern...
            let span = self.tcx.location_store.get_span(pair.pat).unwrap();

            match pat {
                Pat::Binding(BindingPat { mutability, name, .. }) => {
                    candidate.bindings.push(Binding {
                        span,
                        mutability: (*mutability).into(),
                        source: pair.place.into_place(),
                        name: *name,

                        // @@Todo: introduce a way of specifying what the binding
                        // mode of a particular binding is, but for now we assume that
                        // it is always by value.
                        mode: BindingMode::ByValue,
                    });

                    // @@SubPatterns: we don't currently support sub-patterns in bindings, i.e.
                    // when a pattern binds a sub-pattern: `x @ (y, z)` where `(y, z)` is the
                    // sub patterns. When this is added, we need to push all of the
                    // sub-patterns into the `pats` of the candidate so that they can be dealt with.

                    Ok(())
                }
                Pat::Range(RangePat { lo, hi, end }) => {
                    // get the range and bias of this range pattern from
                    // the `lo`
                    let lo_ty = self.lower_term(*lo);
                    // let lo_ty_id = self.storage.ty_store().create(lo_ty);

                    // The range is the minimum value, maximum value, and the size of
                    // the item that is being compared.
                    //
                    // @@Todo: deal with big-ints
                    let (range, bias) = match lo_ty {
                        IrTy::Char => (
                            Some(('\u{0000}' as u128, '\u{10FFFF}' as u128, Size::from_bytes(4))),
                            0,
                        ),
                        IrTy::Int(int_ty) => {
                            let size = int_ty.size(self.tcx.target_pointer_width).unwrap();
                            let max = size.truncate(u128::MAX);
                            let bias = 1u128 << (size.bits() - 1);
                            (Some((0, max, size)), bias)
                        }
                        IrTy::UInt(uint_ty) => {
                            let size = uint_ty.size(self.tcx.target_pointer_width).unwrap();
                            let max = size.truncate(u128::MAX);
                            (Some((0, max, size)), 0)
                        }
                        _ => (None, 0),
                    };

                    // We want to compare ranges numerically, but the order of the bitwise
                    // representation of signed integers does not match their numeric order. Thus,
                    // to correct the ordering, we need to shift the range of signed integers to
                    // correct the comparison. This is achieved by XORing with a bias.
                    if let Some((min, max, size)) = range {
                        let term_to_val = |term: TermId| -> u128 {
                            self.tcx.term_store.map_fast(*lo, |term| match term {
                                Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => {
                                    CONSTANT_MAP.map_int_constant(*value, |val| {
                                        u128::from_be_bytes(val.get_bytes())
                                    })
                                }
                                _ => unreachable!(),
                            })
                        };

                        // we have to convert the `lo` term into the actual value, by getting
                        // the literal term from this term, and then converting the stored value
                        // into a u128...
                        let lo_val = term_to_val(*lo) ^ bias;

                        if lo_val <= min {
                            let hi_val = term_to_val(*hi) ^ bias;

                            // In this situation, we have an irrefutable pattern, so we can
                            // always go down this path
                            if hi_val > max || hi_val == max && *end == RangeEnd::Excluded {
                                return Ok(());
                            }
                        }
                    }

                    Err(pair)
                }
                Pat::Tuple(pat_args) => {
                    // get the type of the tuple so that we can read all of the
                    // fields
                    let ty = self.ty_of_pat(pair.pat);
                    let adt = self.storage.ty_store().map_fast(ty, IrTy::as_adt);

                    candidate.pairs.extend(self.match_pat_fields(*pat_args, adt, pair.place));
                    Ok(())
                }
                Pat::Constructor(ConstructorPat { subject, args }) => {
                    let ty = self.convert_term_into_ir_ty(*subject);
                    let adt = self.map_on_adt(ty, |adt, id| adt.flags.is_struct().then_some(id));

                    // If this is a struct then we need to match on the fields of
                    // the struct since it is an *irrefutable* pattern.
                    if let Some(adt_id) = adt {
                        candidate.pairs.extend(self.match_pat_fields(*args, adt_id, pair.place));
                        return Ok(());
                    }

                    Err(pair)
                }
                Pat::Access(_) | Pat::Const(_) => {
                    // @@Todo: when we switch to the new pattern representation, we can
                    //         remove this branch entirely, for now ignore it.
                    Ok(())
                }
                // The simplification that can occur here is if both the prefix and the
                // suffix are empty, then we can perform some simplifications.
                Pat::List(list_pat) => {
                    let (prefix, suffix, rest) = list_pat.into_parts(self.tcx);

                    if prefix.is_empty() && suffix.is_empty() && rest.is_some() {
                        let ty = self.ty_of_pat(pair.pat);

                        // This means that this is irrefutable since we will always match this
                        // pattern.
                        self.adjust_list_pat_candidates(
                            ty,
                            &mut candidate.pairs,
                            &pair.place,
                            &prefix,
                            rest,
                            &suffix,
                        );

                        Ok(())
                    } else {
                        Err(pair)
                    }
                }

                // We essentially create a new bind for the tuple here
                // that captures all of the members. We create a new bind
                // with the type of this `spread` type which is derived
                // during typechecking...
                Pat::Spread(SpreadPat { name: Some(name) }) => {
                    candidate.bindings.push(Binding {
                        span,
                        // @@FixMe: allow for spread patterns to be declared as `mut`
                        mutability: Mutability::Immutable,
                        name: *name,

                        // @@FixMe: this is not the correct place to use, since we might encounter
                        //           a spread pattern in various locations which means we might
                        //           affect the actual place that is being referenced. This process
                        //           should be alot simpler to do we switch to the new pattern
                        //           representation. This is because, the spreads are now on each
                        //           specific pattern, which means that we can more precisely
                        // determine           the place that we are
                        // referencing.
                        source: pair.place.into_place(),
                        mode: BindingMode::ByRef,
                    });

                    Ok(())
                }

                // We don't need to do anything with this pattern here.
                Pat::Spread(_) | Pat::Mod(_) | Pat::Wild => Ok(()),

                // Look at the pattern located within the if-pat
                Pat::If(IfPat { pat, .. }) => self.simplify_match_pair(
                    MatchPair { pat: pair.pat, place: pair.place.clone() },
                    candidate,
                ),

                // We have to deal with these outside of this function
                Pat::Lit(_) => Err(pair),
                Pat::Or(_) => Err(pair),
            }
        })
    }

    /// Iterate over a list of patterns, and extract the pattern from
    /// all of the arguments. We create new [MatchPair]s for each pattern
    /// that is referenced within the pattern, and automatically adjust
    /// all of the [PlaceProjection]s on the pairs to reflect that they
    /// are performing a field access.
    fn match_pat_fields(
        &mut self,
        pat: PatArgsId,
        ty: AdtId,
        place: PlaceBuilder,
    ) -> Vec<MatchPair> {
        self.storage.adt_store().map_fast(ty, |adt| {
            debug_assert!(adt.flags.is_struct() || adt.flags.is_tuple());

            let variant = adt.variants.first().unwrap();

            self.tcx.pat_args_store.map_as_param_list_fast(pat, |pats| {
                pats.positional()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        // Compute the index we should use to access the field. If
                        // no name is provided, we assume that the type is positional,
                        // and thus we use the index of the pattern in the argument.
                        let index = match arg.name {
                            Some(name) => variant.field_idx(name).unwrap(),
                            None => index,
                        };

                        let place = place.clone_project(PlaceProjection::Field(index));
                        MatchPair { pat: arg.pat, place }
                    })
                    .collect()
            })
        })
    }

    /// Iterate over a set of sub candidates and create a new candidate for each
    /// of them. This function also propagates if any of the above patterns have
    /// an `if` guard around the pattern, in the event that they have to
    /// jump to an `otherwise` case later on during the lowering process.
    fn create_sub_candidates(
        &mut self,
        subject: &PlaceBuilder,
        candidate: &mut Candidate,
        sub_pats: &[PatId],
    ) -> Vec<Candidate> {
        sub_pats
            .iter()
            .copied()
            .map(|pat_id| {
                let pat_has_guard = self.tcx.pat_store.map_fast(pat_id, Pat::is_or);
                let mut sub_candidate = Candidate::new(
                    candidate.span,
                    pat_id,
                    subject,
                    candidate.has_guard || pat_has_guard,
                );
                self.simplify_candidate(candidate);
                sub_candidate
            })
            .collect()
    }
}