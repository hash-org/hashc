//! Hash Compiler Typecheck pattern refutability checking algorithm.
//!
//! The goal of this algorithm to very simply implement a check if a pattern is
//! refutable or isn't. When we say refutable, we mean that given any instance
//! of an expression, can the expression always be matched to the given pattern
//! or are there cases where destructuring the expression into the pattern doesn't
//! work. If there are cases where it cannot be proven that a pattern is irrefutable, this
//! becomes an error and should be reported back to the compiler.
//!
//! *NOTE* The algorithm that is implemented here is a vast simplification and incorrect
//! implementation of a true refutability checking algorithm. The algorithm cannot account for
//! complicated cases of nested types or complex or patterns that might actually be
//! irrefutable, but the algorithm cannot be certain of this.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_ast::ast::{NamespacePattern, Pattern, StructPattern};

/// This algorithm is used to perform a very basic irrefutability check on the provided pattern.
/// Essentially, there are two kinds of patterns that this algorithm views: patterns that are singular
/// and bottom patterns (have no further variants), and patterns that might contain inner patterns (e.g a tuple pattern).
/// For bottom patterns, bindings are not rejected and everything else is rejected because it cannot be proven
/// to be irreducible. For patterns with inner variants, we check that all inner patterns are irreducible and
/// conclude that the parent pattern must be irreducible if all of it's children are irreducible.
/// However, the algorithm does not catch "irrefutable" cases with if-patterns and or-patterns that might
/// have all variants covered and correctly matched. This algorithm is only capable of ensuring that struct,
/// namespace patterns and binds are definitely irrefutable.
pub fn is_pattern_irrefutable(pattern: &Pattern<'_>) -> bool {
    match pattern {
        Pattern::Namespace(NamespacePattern { fields })
        | Pattern::Struct(StructPattern { fields, .. }) => fields
            .iter()
            .all(|x| is_pattern_irrefutable(x.body().pattern.body())),
        Pattern::Binding(_) | Pattern::Ignore(_) => true,
        _ => false,
    }
}
