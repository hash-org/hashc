//! Semantic analysis diagnostic origin data types definitions. The origin
//! of an error in regards to a particular pattern, block or field type
//! is recorded using the defined data types within this module.

use std::fmt::Display;

/// Denotes where a pattern was used as in the parent of the pattern. This is
/// useful for propagating errors upwards by signalling what is the current
/// parent of the pattern. This only contains patterns that can be compound
/// (hold multiple children patterns).
#[derive(Clone, Copy, Debug)]
pub(crate) enum PatOrigin {
    /// The parent is a tuple, i.e `(x, 1, 2)`
    Tuple,
    /// The parent is a pseudo-pattern originating as a named field of some
    /// other parent pattern. Named fields could occur within tuples or
    /// constructor patterns, i.e `Bar(max = 123)`, where the `max` would be
    /// the named field.
    NamedField,
    /// The parent pattern is a constructor, i.e `Some(x)`
    Constructor,
    /// The parent pattern is a list, i.e `[1, 2, 3, ...]`
    List,
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
            PatOrigin::List => "list",
            PatOrigin::Namespace => "namespace",
        }
    }
}

impl Display for PatOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

/// Denotes where an error occurred from which type of block. This is useful
/// when giving more context about errors such as
/// [crate::diagnostics::error::AnalysisErrorKind::NonDeclarativeExpression]
/// occur from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BlockOrigin {
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
