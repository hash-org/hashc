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
    /// Convert the [BlockOrigin] into a string which can be used for displaying
    /// within error messages.
    fn to_str(self) -> &'static str {
        match self {
            BlockOrigin::Root | BlockOrigin::Mod => "module",
            BlockOrigin::Impl => "impl",
            BlockOrigin::Body => "body",
            BlockOrigin::Trait => "trait",
            BlockOrigin::Const => "constant",
        }
    }
}

impl Default for BlockOrigin {
    fn default() -> Self {
        BlockOrigin::Root
    }
}

impl Display for BlockOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
