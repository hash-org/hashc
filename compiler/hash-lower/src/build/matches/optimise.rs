//! Contains various functions that attempt to optimise the
//! generated [Candidate]s so that we minimise the number of
//! tests that we generate.

use std::mem;

use hash_source::location::Span;

use super::candidate::Candidate;
use crate::build::Builder;

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
}
