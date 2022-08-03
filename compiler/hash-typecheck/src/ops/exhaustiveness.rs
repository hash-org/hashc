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
//! all the possibilities of the type `(u32, char)` which is the type
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

use crate::{
    diagnostics::error::TcResult,
    storage::{
        primitives::{PatId, TermId},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

/// Contains actions related to pattern exhaustiveness and usefulness checking.
pub struct ExhaustivenessChecker<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for ExhaustivenessChecker<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for ExhaustivenessChecker<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> ExhaustivenessChecker<'gs, 'ls, 'cd, 's> {
    /// Create a new [ExhaustivenessChecker].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Checks whether a `match` block is exhaustive from the provided patterns
    /// of each branch and whether there are any `useless` patterns that
    /// are present within the
    pub fn is_match_exhaustive(&mut self, _pats: &[PatId], _term: TermId) -> TcResult<()> {
        todo!()
    }

    /// Checks whether the given [PatId] is irrefutable in terms of the provided
    /// [TermId] which will be used as the subject of the refutability check.
    ///
    /// The function takes a list of [PatId]s because some of the cases that
    /// are checked for irrefutability are transpiled into a match block to
    /// avoid being more complicated than they are needed. This process
    /// occurs in [ast desugaring](hash_ast_desugaring::desugaring) module.
    pub fn is_pat_irrefutable(
        &mut self,
        _pats: &[PatId],
        _term: TermId,
        origin: Option<MatchOrigin>,
    ) -> TcResult<()> {
        if let Some(origin) = origin {
            // We shouldn't be checking irrefutability if the origin
            // is a match block...
            assert!(origin != MatchOrigin::Match);
        } else {
        }

        todo!()
    }
}
