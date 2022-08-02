#![allow(unused)] // @@Todo: remove when integrated with tc-visitor

use crate::storage::AccessToStorage;

use self::{
    construct::ConstructorOps, deconstruct::DeconstructPatOps, fields::FieldOps,
    lower::PatLowerOps, matrix::MatrixOps, range::IntRangeOps, stack::StackOps,
    usefulness::UsefulnessOps, wildcard::SplitWildcardOps,
};

mod constant;
pub mod structures;

mod fields;
mod lower;
mod matrix;
mod range;
mod stack;
mod wildcard;

// Needs to be public since we expose `DeconstructPat`
pub mod construct;
pub mod deconstruct;
pub mod usefulness;

/// Trait to access various structures that can perform usefulness queries,
/// by a reference to a [StorageRef](crate::storage::StorageRef).
pub(crate) trait AccessToUsefulnessOps: AccessToStorage {
    // Create an instance of [DeconstructPatOps].
    fn deconstruct_pat_ops(&self) -> DeconstructPatOps {
        DeconstructPatOps::new(self.storages())
    }

    /// Create an instance of [ConstructorOps].
    fn constructor_ops(&self) -> ConstructorOps {
        ConstructorOps::new(self.storages())
    }

    /// Create an instance of [FieldOps].
    fn fields_ops(&self) -> FieldOps {
        FieldOps::new(self.storages())
    }

    /// Create an instance of [PatLowerOps].
    fn pat_lowerer(&self) -> PatLowerOps {
        PatLowerOps::new(self.storages())
    }

    /// Create an instance of [MatrixOps].
    fn matrix_ops(&self) -> MatrixOps {
        MatrixOps::new(self.storages())
    }

    /// Create an instance of [IntRangeOps].
    fn int_range_ops(&self) -> IntRangeOps {
        IntRangeOps::new(self.storages())
    }

    /// Create an instance of [StackOps].
    fn stack_ops(&self) -> StackOps {
        StackOps::new(self.storages())
    }

    /// Create an instance of [UsefulnessOps].
    fn usefulness_ops(&self) -> UsefulnessOps {
        UsefulnessOps::new(self.storages())
    }

    /// Create an instance of [SplitWildcardOps].
    fn split_wildcard_ops(&self) -> SplitWildcardOps {
        SplitWildcardOps::new(self.storages())
    }
}

impl<T: AccessToStorage> AccessToUsefulnessOps for T {}
