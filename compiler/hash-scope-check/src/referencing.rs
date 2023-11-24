//! Definitions to track the usage of a variable.
//!
//! Approach for usages is based on the following paper:
//! Reynaud, Alban, Gabriel Scherer, and Jeremy Yallop. 2021. “A Practical Mode
//! System for Recursive Definitions.” Proc. ACM Program. Lang., 45, 5 (POPL):
//! 1–29.

/// The usage of some term in Hash.
///
/// Usages are ordered by their appearance below.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Usage {
    /// The term is not used at all.
    Ignore,
    /// The term is used in a deferred context, for example inside a function.
    Delay,
    /// The term is immediately put inside some data structure.
    Guard,
    /// The term is immediately "returned" without further usage.
    Return,
    /// The term is immediately inspected in arbitrary ways.
    Dereference,
}

impl Usage {
    /// Compose two usages.
    ///
    /// Conceptually, `compose(n, m)` calculates the usage of a term which has
    /// prior usage `n` but is used in a context which requires usage `m`.
    pub fn compose(self, m: Usage) -> Usage {
        match (self, m) {
            (_, Usage::Ignore) | (Usage::Ignore, _) => Usage::Ignore,
            (Usage::Delay, _) => Usage::Delay,
            (Usage::Guard, Usage::Return) => Usage::Guard,
            (Usage::Guard, m) => m,
            (Usage::Return, m) => m,
            (Usage::Dereference, _) => Usage::Dereference,
        }
    }

    /// Whether this usage is at least as strong as another usage.
    pub fn can_use_as(self, mp: Usage) -> bool {
        self > mp
    }
}
