//! Hash Typechecker exhaustiveness and usefulness checking
//! implementation. This module contains the needed data
//! structures and logic to implement pattern exhaustiveness and usefulness
//! checking.

#![allow(unused)] // @@Todo: remove when integrated with tc-visitor

pub mod constant;
pub mod construct;
pub mod deconstruct;
pub mod fields;
pub mod list;
pub mod lower;
pub mod matrix;
pub mod range;
pub mod stack;
pub mod usefulness;
pub mod wildcard;

use hash_source::location::Span;

use crate::storage::{primitives::TermId, AccessToStorage};

use self::{
    construct::ConstructorOps, deconstruct::DeconstructPatOps, fields::FieldOps,
    lower::PatLowerOps, matrix::MatrixOps, range::IntRangeOps, stack::StackOps,
    usefulness::UsefulnessOps, wildcard::SplitWildcardOps,
};

/// General exhaustiveness context that's used when performing
/// splitting and specialisation operations.
#[derive(Copy, Clone)]
pub struct PatCtx {
    /// The term of the current column that is under investigation
    pub ty: TermId,
    /// Span of the current pattern under investigation.
    pub(super) span: Span,
    /// Whether the current pattern is the whole pattern as found in a match
    /// arm, or if it's a sub-pattern.
    pub(super) is_top_level: bool,
}

impl PatCtx {
    /// Create a new [PatCtx]
    pub fn new(ty: TermId, span: Span, is_top_level: bool) -> Self {
        PatCtx { ty, span, is_top_level }
    }
}

/// Trait to access various structures that can perform usefulness queries,
/// by a reference to a [StorageRef](crate::storage::StorageRef).
pub(crate) trait AccessToUsefulnessOps: AccessToStorage {
    /// Create an instance of [DeconstructPatOps].
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
