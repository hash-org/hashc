//! Auxiliary data structures for denoting where common AST nodes are located
//! and which context they are used in.

use std::fmt::Display;

/// Denotes the current block kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockOrigin {
    /// Root block of the file.
    Root,

    /// The block is a `mod` block.
    Mod,

    /// The block is from a `trait` definition.
    Trait,

    /// The block is an `impl` block.
    Impl,

    /// Block is a body of some kind.
    Body,

    /// A dummy [BlockOrigin] kind, only used for error
    /// reporting and grouping `constant` blocks together.
    Const,
}

impl BlockOrigin {
    /// Check if the [BlockOrigin] is constant.
    pub fn is_const(&self) -> bool {
        !matches!(self, BlockOrigin::Body)
    }
}

impl Display for BlockOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlockOrigin::Root | BlockOrigin::Mod => write!(f, "module"),
            BlockOrigin::Impl => write!(f, "impl"),
            BlockOrigin::Body => write!(f, "body"),
            BlockOrigin::Trait => write!(f, "trait"),
            BlockOrigin::Const => write!(f, "constant"),
        }
    }
}
