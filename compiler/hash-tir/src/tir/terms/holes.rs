//! Definitions related to term holes.

use core::fmt;

use crate::tir::{NodeOrigin, SymbolId};

/// A hole, or in other words a variable which will be resolved as a term later.
///
/// This is the basis of the type inference mechanism; the type checker will
/// create holes when it does not know something (such as the type of a term),
/// and then it will fill those holes once it has enough information to do so.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Hole(pub SymbolId);

impl Hole {
    /// Create a new hole.
    pub fn fresh(origin: NodeOrigin) -> Self {
        Self(SymbolId::fresh(origin))
    }
}

impl fmt::Display for Hole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "h{}", self.0)
    }
}
