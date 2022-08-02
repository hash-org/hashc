use smallvec::{smallvec, SmallVec};

use crate::{
    exhaustiveness::structures::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
};

use super::AccessToUsefulnessOps;

/// A row of a matrix. Rows of len 1 are very common, which is why
/// `SmallVec[_; /// 2]` works well.
#[derive(Clone)]
pub struct PatStack {
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

pub struct StackOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for StackOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> StackOps<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
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

    /// This computes `S(self.head().ctor(), self)`. See top of the file for
    /// explanations.
    ///
    ///
    /// @@Todo: Structure patterns with a partial wild pattern `Foo(a: 42,..)`
    /// have their missing fields filled with wild patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    pub(crate) fn pop_head_constructor(
        &mut self,
        ctx: PatCtx,
        stack: &PatStack,
        ctor: ConstructorId,
    ) -> PatStack {
        // We pop the head pattern and push the new fields extracted from the arguments
        // of `self.head()`.
        let mut new_fields: SmallVec<[_; 2]> =
            self.deconstruct_pat_ops().specialise(ctx, stack.head(), ctor);
        new_fields.extend_from_slice(&stack.pats[1..]);

        PatStack::from_vec(new_fields)
    }
}
