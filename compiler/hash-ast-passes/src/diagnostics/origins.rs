//! Semantic analysis diagnostic origin data types definitions. The origin
//! of an error in regards to a particular pattern, block or field type
//! is recorded using the defined data types within this module.

use std::fmt::Display;

/// Denotes where a pattern was used as in the parent of the pattern. This is
/// useful for propagating errors upwards by signalling what is the current
/// parent of the pattern. This only contains patterns that can be compound
/// (hold multiple children patterns).
#[derive(Clone, Copy, Debug)]
pub(crate) enum PatternOrigin {
    Tuple,
    NamedField,
    Constructor,
    List,
    Namespace,
}

impl PatternOrigin {
    /// Convert the [PatternOrigin] into a string which can be used for
    /// displaying within error messages.
    fn to_str(self) -> &'static str {
        match self {
            PatternOrigin::Tuple => "tuple",
            PatternOrigin::NamedField => "named field",
            PatternOrigin::Constructor => "constructor",
            PatternOrigin::List => "list",
            PatternOrigin::Namespace => "namespace",
        }
    }
}

impl Display for PatternOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

/// Denotes where an error occurred from which type of block. This is useful
/// when giving more context about errors such as
/// [AnalysisErrorKind::NonDeclarativeExpression] occur from.
#[derive(Clone, Copy, Debug)]
pub(crate) enum BlockOrigin {
    Root,
    Mod,
    Impl,
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

/// Denotes where an error occurred in regards to a field within a defined
/// structural type which contains fields, such as `struct`, `tuple`, or
/// `function literal`.
#[derive(Clone, Copy, Debug)]
pub(crate) enum FieldOrigin {
    Struct,
    Tuple,
    FnLiteral,
}

impl FieldOrigin {
    /// Convert the [BlockOrigin] into a string which can be used for displaying
    /// within error messages.
    fn to_str(self) -> &'static str {
        match self {
            FieldOrigin::Struct => "struct",
            FieldOrigin::Tuple => "tuple",
            FieldOrigin::FnLiteral => "function literal",
        }
    }
}

impl Display for FieldOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
