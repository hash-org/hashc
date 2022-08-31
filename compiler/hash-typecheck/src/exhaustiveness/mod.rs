//! Hash Typechecker pattern exhaustiveness module. This module contains all
//! of the machinery that is responsible for validating the exhaustiveness and
//! usefulness of patterns.
//!
//! Usefulness and exhaustiveness are inherently linked concepts, and are
//! computed in at the same time. In terms of `usefulness` we compute that if a
//! specified pattern `p` is useful in regards to a row of patterns `v` which
//! precede `p`. In other words, will this pattern `p` be ever reached if the
//! patterns `v` are specified before it. Usefulness determines if certain
//! branches in a `match` statement or other constructs that utilise patterns
//! will ever be matched.
//!
//! Exhaustiveness is similar to usefulness, but addresses the question of will
//! the provided row of patterns `v` cover all variants of some subject type.
//! For example, in the `match` block:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(_) => print("there is a number");
//!     None => print("there is no number");
//! };
//! ```
//!
//! So in this example, for `x` which is of type `Option<i32>`, will the
//! patterns: [`Some(_)`, `None`] cover all cases of `Option<i32>`. In this
//! situation yes, because both variants and their inner constructors because of
//! the wildcard `_`. However, a case where this property does not hold can be
//! easily constructed:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(3) => print("The number is 3!");
//!     None => print("there is no number");
//! };
//! ```
//!
//! Well here, we can come up with cases which the pattern set does not cover,
//! for example `Some(4)`. Therefore, the exhaustiveness check will conclude
//! that the provided pattern vector is not exhaustive and misses some cases.
//!
//! The implementation of this algorithm is based on the research paper:
//!
//! <http://moscova.inria.fr/~maranget/papers/warn/warn.pdf>
//!
//! inspired by and based off of the Rust Compiler implementation:
//!
//! <https://github.com/rust-lang/rust/tree/master/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs>

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

use hash_types::terms::TermId;

use self::{
    construct::ConstructorOps, deconstruct::DeconstructPatOps, fields::FieldOps,
    lower::LowerPatOps, matrix::MatrixOps, range::IntRangeOps, stack::StackOps,
    usefulness::UsefulnessOps, wildcard::SplitWildcardOps,
};
use crate::{
    fmt::TcFormatOpts,
    storage::{AccessToStorage, StorageRef},
};

/// General exhaustiveness context that's used when performing
/// splitting and specialisation operations.
#[derive(Copy, Clone)]
pub struct PatCtx {
    /// The term of the current column that is under investigation
    pub ty: TermId,
    /// Whether the current pattern is the whole pattern as found in a match
    /// arm, or if it's a sub-pattern.
    pub(super) is_top_level: bool,
}

impl PatCtx {
    /// Create a new [PatCtx]
    pub fn new(ty: TermId, is_top_level: bool) -> Self {
        PatCtx { ty, is_top_level }
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

    /// Create an instance of [LowerPatOps].
    fn pat_lowerer(&self) -> LowerPatOps {
        LowerPatOps::new(self.storages())
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

/// Wraps a type `T` in a structure that contains information to be able to
/// format `T` using [TcFormatter].
///
/// This can wrap any type, but only types that have corresponding `fmt_*`
/// methods in [TcFormatter] are useful with it.
pub struct PatForFormatting<'tc, T> {
    pub item: T,
    pub storage: StorageRef<'tc>,
    pub opts: TcFormatOpts,
}

/// Convenience trait to create a `ForFormatting<T>` given a `T`.
pub trait PreparePatForFormatting: Sized {
    /// Create a [PatForFormatting<T>] given a `T`.
    fn for_formatting(self, storage: StorageRef<'_>) -> PatForFormatting<Self> {
        PatForFormatting { item: self, storage, opts: TcFormatOpts::default() }
    }

    /// Create a [PatForFormatting<T>] given a `T`, and provide an out parameter
    /// for the `is_atomic` check.
    fn pat_for_formatting_with_opts(
        self,
        storage: StorageRef<'_>,
        opts: TcFormatOpts,
    ) -> PatForFormatting<Self> {
        PatForFormatting { item: self, storage, opts }
    }
}
