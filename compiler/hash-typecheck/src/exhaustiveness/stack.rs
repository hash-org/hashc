//! Exhaustiveness stack data structure, which is used
//! to represent [super::matrix::Matrix] rows. This file
//! contains some utilities on the [PatStack] to perform
//! transformations, and [StackOps] contains functions
//! that are relevant to the usefulness and exhaustiveness
//! algorithm.
use std::fmt::Debug;

use smallvec::{smallvec, SmallVec};

use super::AccessToUsefulnessOps;
use crate::{
    exhaustiveness::PatCtx,
    fmt::{ForFormatting, PrepareForFormatting},
    ops::AccessToOps,
    storage::{
        deconstructed::{DeconstructedCtorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
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

pub struct StackOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for StackOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> StackOps<'tc> {
    /// Create an instance of [StackOps]
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Recursively expand the first pattern into its sub-patterns. Only useful
    /// if the pattern is an or-pattern.
    ///
    /// Panics if `self` is empty.
    pub(crate) fn expand_or_pat(&self, stack: &PatStack) -> Vec<PatStack> {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat(stack.head());

        pat.fields
            .iter_patterns()
            .map(move |pat| {
                let mut new_stack = PatStack::singleton(*pat);

                new_stack.pats.extend_from_slice(&stack.pats[1..]);
                new_stack
            })
            .collect()
    }

    /// This computes `S(self.head().ctor, self)`. Take the head of
    /// the [PatStack], specialise it with the provided `ctor` and
    /// and build a new [PatStack] with the result of the specialisation
    /// and the rest of the row items.
    ///
    /// @@Future: Structure patterns with a partial wild pattern `Foo(a: 42,
    /// ..)` have their missing fields filled with wild patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    pub(crate) fn pop_head_constructor(
        &mut self,
        ctx: PatCtx,
        stack: &PatStack,
        ctor: DeconstructedCtorId,
    ) -> PatStack {
        // We pop the head pattern and push the new fields extracted from the arguments
        // of `self.head()`.
        let mut new_fields: SmallVec<[_; 2]> =
            self.deconstruct_pat_ops().specialise(ctx, stack.head(), ctor);

        new_fields.extend_from_slice(&stack.pats[1..]);

        PatStack::from_vec(new_fields)
    }
}

impl PrepareForFormatting for PatStack {}

impl Debug for ForFormatting<'_, PatStack> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "|")?;

        for pat in self.t.iter() {
            write!(f, " {:?} |", pat.for_formatting(self.global_storage))?;
        }

        Ok(())
    }
}
