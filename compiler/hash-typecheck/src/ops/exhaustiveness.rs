//! Provides an interface between the exhaustiveness sub-system
//! and the general typechecker. This file contains functions
//! that allow the typechecker to query whether patterns are
//! exhaustive or irrefutable.
//!
//! ## Irrefutability
//!
//! Irrefutability means that for a given pattern `p` and a type `t`,
//! will the pattern `p` match all possible variants of `t`. This
//! is important in situations where pattern matching should
//! guarantee only a single variant, for example in a `declaration`
//! or a `for-loop`:
//!
//! ```ignore
//! 
//! ts := [(0, 'c'), (1, 'a'), (2, 'b')];
//!
//! for (key, value) in ts {
//!     ...
//! }
//! ```
//!
//! The above pattern `(key, value)` is irrefutable because it covers
//! all the possibilities of the type `(i32, char)` which is the type
//! of the list element. However, in the situation that the pattern
//! was for example `(key, 'c')`, well for any time that `char` is
//! not a `c`, this match will fail, which means the pattern is refutable
//! and cannot be used in cases where irrefutable patterns are required.
//!
//! ## Exhaustiveness
//!
//! Exhaustiveness is a similar concept, but assumes that a collection
//! of patterns must be irrefutable or in other words exhaust all possible
//! values the provided subject. Exhaustiveness checking is performed
//! on match-blocks in order to check that they are exhaustive. More details
//! about the exhaustiveness check algorithm are within the
//! [exhaustiveness](crate::exhaustiveness) module.
use hash_ast::ast::MatchOrigin;
use hash_utils::store::Store;
use itertools::Itertools;

use super::AccessToOps;
use crate::{
    diagnostics::error::{TcError, TcResult},
    exhaustiveness::{usefulness::MatchArm, AccessToUsefulnessOps},
    storage::{pats::PatId, primitives::Pat, terms::TermId, AccessToStorage, StorageRef},
};

/// Contains actions related to pattern exhaustiveness and usefulness checking.
pub struct ExhaustivenessChecker<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for ExhaustivenessChecker<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> ExhaustivenessChecker<'tc> {
    /// Create a new [ExhaustivenessChecker].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    fn lower_pats_to_arms(&self, pats: &[PatId], term: TermId) -> Vec<MatchArm> {
        let reader = self.reader();

        pats.iter()
            .map(|id| {
                let prim_pat = reader.get_pat(*id);

                let destructed_pat = self.pat_lowerer().deconstruct_pat(term, *id);
                let pat = self.deconstructed_pat_store().create(destructed_pat);

                MatchArm { pat, has_guard: matches!(prim_pat, Pat::If(_)) }
            })
            .collect_vec()
    }

    /// Checks whether a `match` block is exhaustive from the provided patterns
    /// of each branch and whether there are any `useless` patterns that
    /// are present within the
    pub fn is_match_exhaustive(&self, pats: &[PatId], term: TermId) -> TcResult<()> {
        let arms = self.lower_pats_to_arms(pats, term);
        let report = self.usefulness_ops().compute_match_usefulness(term, &arms);

        // @@Todo: deal with arm reachability in the form of generating
        // warnings in the discussed diagnostic system.
        let witnesses = report.non_exhaustiveness_witnesses;

        if witnesses.is_empty() {
            Ok(())
        } else {
            Err(TcError::NonExhaustiveMatch { term, uncovered_pats: witnesses })
        }
    }

    /// Checks whether the given [PatId] is irrefutable in terms of the provided
    /// [TermId] which will be used as the subject of the refutability check.
    ///
    /// The function takes a list of [PatId]s because some of the cases that
    /// are checked for irrefutability are transpiled into a match block to
    /// avoid being more complicated than they are needed. This process
    /// occurs in [ast desugaring](hash_ast_desugaring::desugaring) module.
    pub fn is_pat_irrefutable(
        &self,
        pats: &[PatId],
        term: TermId,
        origin: Option<MatchOrigin>,
    ) -> TcResult<()> {
        let arms = self.lower_pats_to_arms(pats, term);
        let report = self.usefulness_ops().compute_match_usefulness(term, &arms);

        // We ignore whether the pattern is unreachable (i.e. whether the type is
        // empty). We only care about exhaustiveness here.
        let witnesses = report.non_exhaustiveness_witnesses;

        if witnesses.is_empty() {
            Ok(())
        } else {
            Err(TcError::RefutablePat { origin, pat: pats[0], uncovered_pats: witnesses })
        }
    }
}
