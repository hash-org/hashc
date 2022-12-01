//! Module that contains all of the logic with dealing with `match` blocks.
//! Lowering `match` blocks is probably the most complex part of lowering, since
//! we have to create essentially a *jump* table each case that is specified in
//! the `match` arms, which might also have `if` guards, `or` patterns, etc.
#![allow(unused, dead_code)]

use std::{borrow::Borrow, mem};

use hash_ast::ast::{AstNodeRef, Expr, MatchCase};
use hash_ir::{
    ir::{BasicBlock, Place, TerminatorKind},
    ty::{IrTy, Mutability},
};
use hash_source::{constant::CONSTANT_MAP, location::Span};
use hash_target::size::Size;
use hash_types::{
    pats::{BindingPat, IfPat, Pat, PatId, RangePat, SpreadPat},
    terms::{Level0Term, LitTerm, Term, TermId},
};
use hash_utils::{stack::ensure_sufficient_stack, store::Store};
use smallvec::{smallvec, SmallVec};

use super::{place::PlaceBuilder, ty::lower_term, unpack, BlockAnd, BlockAndExtend, Builder};

pub struct Candidate {
    /// The span of the `match` arm, for-error reporting
    /// functionality.
    pub span: Span,

    /// Whether or not the candidate arm hsa an associated guard,
    pub has_guard: bool,

    /// All the bindings that are created in the candidate arm.
    pub bindings: Vec<Binding>,

    /// The match pair that is associated with the binding.
    pub pats: SmallVec<[PatId; 1]>,

    ///
    pub otherwise_block: Option<BasicBlock>,
    ///
    pub pre_binding_block: Option<BasicBlock>,
    ///
    pub next_candidate_pre_bind_block: Option<BasicBlock>,

    /// Any sub-candidates that are associated with this candidate.
    pub sub_candidates: Vec<Candidate>,
}

impl Candidate {
    /// Create a new [Candidate].
    pub fn new(span: Span, pat: PatId, has_guard: bool) -> Self {
        Self {
            span,
            has_guard,
            otherwise_block: None,
            pre_binding_block: None,
            next_candidate_pre_bind_block: None,
            // @@Todo: do we need to store an associated place with this pattern?
            pats: smallvec![pat],
            bindings: Vec::new(),
            sub_candidates: Vec::new(),
        }
    }

    /// Visit all of the leaves of a candidate and apply some operation on
    /// each one that is contained in the current candidate.
    pub fn visit_leaves<'a>(&'a mut self, mut visit_leaf: impl FnMut(&'a mut Candidate)) {
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
fn traverse_candidate<C, T, I>(
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
pub struct Binding {
    /// The span of the binding.
    pub span: Span,

    // @@Todo: do we need to store an associated place with the pattern?
    //
    // The source of the binding, where the value is coming from.
    // pub place: Place,
    /// The mutability of the binding
    pub mutability: Mutability,

    /// The mode of the bind, whether it is by reference or by the value.
    pub mode: BindingMode,
}

#[derive(Debug, Clone, Copy)]
pub enum BindingMode {
    ByValue,
    ByRef,
}

type Candidates<'tcx> = (AstNodeRef<'tcx, MatchCase>, Candidate);

impl<'tcx> Builder<'tcx> {
    /// This is the entry point of matching an expression. Firstly, we deal with
    /// the subject of the match, and then we build a decision tree of all
    /// of the arms that have been specified, then we create all of the
    /// blocks that are required to represent the decision tree. After the
    /// decision tree has been built, we then build the blocks
    /// that are required to represent the actual match arms.
    pub(crate) fn match_expr(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        subject: AstNodeRef<'tcx, Expr>,
        arms: Vec<AstNodeRef<'tcx, MatchCase>>,
    ) -> BlockAnd<()> {
        let subject_place =
            unpack!(block = self.as_place_builder(block, subject, Mutability::Immutable));

        // Make the decision tree here...
        let mut arm_candidates = self.create_match_candidates(&arms);

        let mut candidates =
            arm_candidates.iter_mut().map(|(_, candidate)| candidate).collect::<Vec<_>>();

        // Using the decision tree, now build up the blocks for each arm, and then
        // join them at the end to the next block after the match, i.e. the `ending
        // block`.
        let ending_block = self.lower_match_arms(
            block,
            destination,
            subject_place,
            subject.span(),
            &mut candidates,
        );

        ending_block.unit()
    }

    fn create_match_candidates(
        &mut self,
        arms: &[AstNodeRef<'tcx, MatchCase>],
    ) -> Vec<Candidates<'tcx>> {
        arms.iter()
            .copied()
            .map(|arm| {
                let pat_id = self.get_pat_id_of_node(arm.pat.id());
                let candidate = Candidate::new(arm.span, pat_id, arm.has_if_pat());
                (arm, candidate)
            })
            .collect()
    }

    fn lower_match_arms(
        &mut self,
        block: BasicBlock,
        destination: Place,
        subject_place: PlaceBuilder,
        subject_span: Span,
        arm_candidates: &mut [&mut Candidate],
    ) -> BasicBlock {
        // This is the basic block that is derived for using when the
        // matching fails on the pattern, and that it should jump to
        // in the `otherwise` situation.
        let mut otherwise = None;

        self.match_candidates(block, &mut otherwise, arm_candidates);

        // We need to terminate the otherwise block with an `unreachable` since
        // this branch should never be reached since the `match` is exhaustive.
        if let Some(otherwise_block) = otherwise {
            self.control_flow_graph.terminate(
                otherwise_block,
                subject_span,
                TerminatorKind::Unreachable,
            );
        }

        todo!()
    }

    /// This is the main **entry point** of the match-lowering algorithm.
    fn match_candidates(
        &mut self,
        block: BasicBlock,
        otherwise: &mut Option<BasicBlock>,
        candidates: &mut [&mut Candidate],
    ) {
        // Start by simplifying the candidates, i.e. splitting them into sub-candidates
        // so that they can be dealt with in a much easier way. If any of the
        // candidates we're split in the simplification process, we need to
        // later re-add them to the `candidates` list so that when they are
        // actually generated, they can be generated for only simple candidates,
        // and that all of them are dealt with.
        let mut split_or_candidate = false;

        for candidate in &mut *candidates {
            split_or_candidate |= self.simplify_candidate(candidate);
        }

        ensure_sufficient_stack(|| {
            if split_or_candidate {
                let mut new_candidates = Vec::new();

                // Iterate over all of the candidates and essentially flatten the
                // candidate list...
                for candidate in candidates {
                    candidate.visit_leaves(|leaf| new_candidates.push(leaf));
                }

                self.match_simplified_candidates(block, otherwise, &mut new_candidates)
            } else {
                self.match_simplified_candidates(block, otherwise, candidates)
            }
        });
    }

    fn match_simplified_candidates(
        &mut self,
        block: BasicBlock,
        otherwise: &mut Option<BasicBlock>,
        candidates: &mut [&mut Candidate],
    ) {
        todo!()
    }

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
    fn simplify_candidate(&mut self, candidate: &mut Candidate) -> bool {
        // keep a record of the existing bindings and all of the bindings that
        // are to be added when exploring the pattern.
        let mut existing_bindings = mem::take(&mut candidate.bindings);
        let mut new_bindings = Vec::new();

        loop {
            let match_pairs = mem::take(&mut candidate.pats);

            // Check if the bindings has a single or-pattern
            if let [pat] = *match_pairs {
                if self.tcx.pat_store.map_fast(pat, Pat::is_or) {
                    // append all the new bindings, and then swap the two vecs around
                    existing_bindings.extend_from_slice(&new_bindings);
                    mem::swap(&mut candidate.bindings, &mut existing_bindings);

                    // Now we need to create sub-candidates for each of the or-patterns
                    return self.tcx.pat_store.map_fast(pat, |pat| {
                        let Pat::Or(sub_pats) = pat else {
                            unreachable!()
                        };

                        candidate.sub_candidates = self.create_sub_candidates(candidate, sub_pats);

                        true
                    });
                }
            }

            // There are multiple patterns to check here, so we need to iterate
            // over each one and perform a simplification...
            let mut changed = false;

            for pat in match_pairs {
                match self.simplify_pat(pat, candidate) {
                    Ok(_) => {
                        changed = true;
                    }
                    // We need to re-evaluate one of the patterns later on
                    Err(pat_id) => candidate.pats.push(pat_id),
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
                candidate.pats.sort_by_key(|pat| self.tcx.pat_store.map_fast(*pat, Pat::is_or));

                // We weren't able to perform any further simplifications, so return false
                return false;
            }
        }
    }

    fn simplify_pat(&mut self, pat_id: PatId, candidate: &mut Candidate) -> Result<(), PatId> {
        self.tcx.pat_store.map_fast(pat_id, |pat| {
            // Get the span of this partciular pattern...
            let span = self.tcx.location_store.get_span(pat_id).unwrap();

            match pat {
                Pat::Binding(BindingPat { mutability, .. }) => {
                    candidate.bindings.push(Binding {
                        span,
                        mutability: (*mutability).into(),
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
                    let lo_ty = lower_term(*lo, self.tcx, self.storage);
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
                        let lo_val = term_to_val(*lo);

                        // let lo = lo.try_to_bits(sz).unwrap() ^ bias;
                    }

                    Err(pat_id)
                }
                Pat::Tuple(_) => todo!(),
                Pat::Access(_) | Pat::Const(_) | Pat::Constructor(_) => todo!(),
                Pat::List(_) => todo!(),

                // We essentially create a new bind for the tuple here
                // that captures all of the members. We create a new bind
                // with the type of this `spread` type which is derived
                // during typechecking...
                Pat::Spread(SpreadPat { name }) if name.is_some() => {
                    candidate.bindings.push(Binding {
                        span,
                        // @@FixMe: allow for spread patterns to be declared as `mut`
                        mutability: Mutability::Immutable,

                        // @@FixMe: is this correct? Since it shouldn't always be passed by
                        // reference into the proceeding block
                        mode: BindingMode::ByRef,
                    });

                    Ok(())
                }

                // We don't need to do anything with this pattern here.
                Pat::Spread(_) | Pat::Mod(_) | Pat::Wild => Ok(()),

                // Look at the pattern located within the if-pat
                Pat::If(IfPat { pat, .. }) => self.simplify_pat(*pat, candidate),

                // We have to deal with these outside of this function
                Pat::Lit(_) => Err(pat_id),
                Pat::Or(_) => Err(pat_id),
            }
        })
    }

    /// Iterate over a set of sub candidates and create a new candidate for each
    /// of them. This function also propagates if any of the above patterns have
    /// an `if` guard around the pattern, in the event that they have to
    /// jump to an `otherwise` case later on during the lowering process.
    fn create_sub_candidates(
        &mut self,
        candidate: &mut Candidate,
        sub_pats: &[PatId],
    ) -> Vec<Candidate> {
        sub_pats
            .iter()
            .copied()
            .map(|pat_id| {
                let pat_has_guard = self.tcx.pat_store.map_fast(pat_id, Pat::is_or);
                let mut sub_candidate =
                    Candidate::new(candidate.span, pat_id, candidate.has_guard || pat_has_guard);
                self.simplify_candidate(candidate);
                sub_candidate
            })
            .collect()
    }
}
