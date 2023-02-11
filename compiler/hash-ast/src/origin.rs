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

/// Denotes where a pattern was used as in the parent of the pattern. This is
/// useful for propagating errors upwards by signalling what is the current
/// parent of the pattern. This only contains patterns that can be compound
/// (hold multiple children patterns).
#[derive(Clone, Copy, Debug)]
pub enum PatOrigin {
    /// The parent is a tuple, i.e `(x, 1, 2)`
    Tuple,

    /// The parent is a pseudo-pattern originating as a named field of some
    /// other parent pattern. Named fields could occur within tuples or
    /// constructor patterns, i.e `Bar(max = 123)`, where the `max` would be
    /// the named field.
    ///
    /// This is primarily used for checking if a collection of patterns (within
    /// a constructor or tuple) don't introduce ambiguous pattern orders when
    /// both named and un-named fields are used.
    NamedField,

    /// The parent pattern is a constructor, i.e `Some(x)`
    Constructor,

    /// The parent pattern is a list, i.e `[1, 2, 3, ...]`
    Array,

    /// The parent pattern is a namespace, i.e `{ alloc, core }`
    Namespace,
}

impl PatOrigin {
    /// Convert the [PatOrigin] into a string which can be used for
    /// displaying within error messages.
    fn to_str(self) -> &'static str {
        match self {
            PatOrigin::Tuple => "tuple",
            PatOrigin::NamedField => "named field",
            PatOrigin::Constructor => "constructor",
            PatOrigin::Array => "array",
            PatOrigin::Namespace => "namespace",
        }
    }
}

impl Display for PatOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
