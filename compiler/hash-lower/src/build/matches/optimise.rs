//! Contains various functions that attempt to optimise the
//! generated [Candidate]s so that we minimise the number of
//! tests that we generate.

use std::mem;

use hash_ir::{
    ir::PlaceProjection,
    ty::{IrTy, IrTyId},
};
use hash_source::location::Span;
use hash_types::pats::PatId;
use smallvec::SmallVec;

use super::candidate::{Candidate, MatchPair};
use crate::build::{place::PlaceBuilder, Builder};

impl<'tcx> Builder<'tcx> {
    /// Attempt to optimise the sub-candidates of a provided [Candidate]. This
    /// only performs a trivial merge, so we avoid generating exponential
    pub(super) fn merge_sub_candidates(&mut self, candidate: &mut Candidate, span: Span) {
        if candidate.sub_candidates.is_empty() {
            return;
        }

        let mut can_merge = false;

        // Check that all of the candidates have no sub-candidates and no-bindings,
        // otherwise this might impact the optimisation.
        //
        // @@Todo: don't give up so easily here.
        for sub_candidate in &mut candidate.sub_candidates {
            self.merge_sub_candidates(sub_candidate, span);

            can_merge &=
                sub_candidate.sub_candidates.is_empty() && sub_candidate.bindings.is_empty();
        }

        if can_merge {
            let any_matches = self.control_flow_graph.start_new_block();

            // Make all of the pre-binding blocks goto the commonly shared
            // candidate `pre_binding` block.
            for sub_candidate in mem::take(&mut candidate.sub_candidates) {
                let or_block = sub_candidate.pre_binding_block.unwrap();
                self.control_flow_graph.goto(or_block, any_matches, span)
            }

            candidate.pre_binding_block = Some(any_matches);
        }
    }

    /// This function is responsible for adjusting all of the inner [MatchPair]s
    /// of a list candidate. This means that when a pair is eliminated, we have
    /// to compute all of the `projections` that occur on the list pattern,
    /// this means that all of the index projections are re-computed, and
    /// the `rest` pattern projection is also adjusted.
    pub(super) fn adjust_list_pat_candidates(
        &mut self,
        ty: IrTyId,
        pairs: &mut SmallVec<[MatchPair; 1]>,
        place: &PlaceBuilder,
        prefix: &[PatId],
        rest: Option<PatId>,
        suffix: &[PatId],
    ) {
        let (min_length, exact_size) = self.map_ty(ty, |ty| match ty {
            IrTy::Array { size, .. } => (*size, true),
            _ => (prefix.len() + suffix.len(), false),
        });

        // Add all of the prefix patterns.
        pairs.extend(prefix.iter().enumerate().map(|(index, sub_pat)| {
            let projection =
                PlaceProjection::ConstantIndex { offset: index, from_end: false, min_length };
            MatchPair { place: place.clone().project(projection), pat: *sub_pat }
        }));

        // Create a projection as a a `sub-slice` of the original array
        if let Some(rest_pat) = rest {
            let suffix_len = suffix.len();
            let place = place.clone_project(PlaceProjection::Subslice {
                from: prefix.len(),
                to: if exact_size { min_length - suffix_len } else { suffix_len },
                from_end: !exact_size,
            });
            pairs.push(MatchPair { place, pat: rest_pat });
        }

        // Add all of the suffixes, with a constant offset, i.e. the size of the
        // prefix.
        pairs.extend(suffix.iter().enumerate().map(|(index, sub_pat)| {
            let offset = if exact_size { min_length - (index + 1) } else { index + 1 };

            let projection =
                PlaceProjection::ConstantIndex { offset, from_end: !exact_size, min_length };
            MatchPair { place: place.clone().project(projection), pat: *sub_pat }
        }));
    }
}
