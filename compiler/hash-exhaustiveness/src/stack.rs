//! Exhaustiveness stack data structure, which is used
//! to represent [super::matrix::Matrix] rows. This file
//! contains some utilities on the [PatStack] to perform
//! transformations, and [StackOps] contains functions
//! that are relevant to the usefulness and exhaustiveness
//! algorithm.
use std::fmt::{self, Debug};

use hash_utils::smallvec::{smallvec, SmallVec};

use crate::{
    storage::{DeconstructedCtorId, DeconstructedPatId},
    ExhaustivenessChecker, ExhaustivenessFmtCtx, PatCtx,
};

/// A row of a [super::matrix::Matrix]. Rows of len 1 are very common, which is
/// why `SmallVec[_; /// 2]` works well.
#[derive(Clone, Debug)]
pub struct PatStack {
    /// The stored patterns in the row.
    pub pats: SmallVec<[DeconstructedPatId; 2]>,
}

impl PatStack {
    // /// Construct a [PatStack] with a single pattern.
    pub fn singleton(pat: DeconstructedPatId) -> Self {
        Self::from_vec(smallvec![pat])
    }

    // /// Construct a [PatStack] from a [SmallVec].
    pub fn from_vec(vec: SmallVec<[DeconstructedPatId; 2]>) -> Self {
        PatStack { pats: vec }
    }

    /// Check whether the current [PatStack] is empty
    pub fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    /// Get the length of the [PatStack]
    pub fn len(&self) -> usize {
        self.pats.len()
    }

    /// Get the head of the current [PatStack]
    pub fn head(&self) -> DeconstructedPatId {
        self.pats[0]
    }

    /// Iterate over the items within the [PatStack].
    pub fn iter(&self) -> impl Iterator<Item = &DeconstructedPatId> {
        self.pats.iter()
    }
}

impl<'tc> ExhaustivenessChecker<'tc> {
    /// Recursively expand the first pattern into its sub-patterns. Only useful
    /// if the pattern is an or-pattern.
    ///
    /// Panics if `self` is empty.
    pub(crate) fn expand_or_pat(&self, stack: &PatStack) -> Vec<PatStack> {
        let pat = self.get_deconstructed_pat(stack.head());

        pat.fields
            .iter_patterns()
            .map(move |pat| {
                let mut new_stack = PatStack::singleton(pat);

                new_stack.pats.extend_from_slice(&stack.pats[1..]);
                new_stack
            })
            .collect()
    }

    /// This computes `S(self.head().ctor, self)`. Take the head of
    /// the [PatStack], specialise it with the provided `ctor` and
    /// and build a new [PatStack] with the result of the specialisation
    /// and the rest of the row items. Structure patterns with a partial wild
    /// pattern `Foo(a = 42, ...)` have their missing fields filled with wild
    /// patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    pub(crate) fn pop_head_ctor(
        &self,
        ctx: PatCtx,
        stack: &PatStack,
        ctor: DeconstructedCtorId,
    ) -> PatStack {
        // We pop the head pattern and push the new fields extracted from the arguments
        // of `self.head()`.
        let mut new_fields: SmallVec<[_; 2]> = self.specialise(ctx, stack.head(), ctor);

        new_fields.extend_from_slice(&stack.pats[1..]);

        PatStack::from_vec(new_fields)
    }
}

impl fmt::Debug for ExhaustivenessFmtCtx<'_, PatStack> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "|")?;

        for pat in self.item.iter() {
            write!(f, " {:?} |", self.with(*pat))?;
        }

        // Just in case if the pattern stack was empty
        if self.item.is_empty() {
            write!(f, "|")?;
        }

        Ok(())
    }
}
