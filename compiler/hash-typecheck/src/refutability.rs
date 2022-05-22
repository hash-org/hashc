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

use hash_ast::ast::{NamespacePattern, Pattern};

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
        Pattern::Namespace(NamespacePattern { fields }) => fields
            .iter()
            .all(|x| is_pattern_irrefutable(x.body().pattern.body())),
        Pattern::Binding(_) | Pattern::Ignore(_) => true,
        // Pattern::Tuple(TuplePattern { fields }) => check_if_pattern_list_is_irrefutable(
        //     fields.iter().map(|node| node.body().pattern.body()),
        // ),
        // Pattern::List(ListPattern { fields }) => {
        //     check_if_pattern_list_is_irrefutable(fields.iter().map(|node| node.body()))
        // }
        Pattern::Spread(_) => true,
        _ => false,
    }
}

// Function to verify that the children of pattern are irrefutable if spread
// patterns are permitted within this pattern construct and therefore they will
// cover all cases in the pattern
// fn check_if_pattern_list_is_irrefutable<'c: 'p, 'p>(
//     mut patterns: impl Iterator<Item = &'p Pattern<'c>>,
// ) -> bool {
//     let mut has_spread = false;

//     // So check that all of the children are irrefutable and if the
//     // pattern contains a spread operator, we can be sure that it covers
//     // all cases of this pattern
//     let all_children_irrefutable = patterns.all(|pattern| {
//         if matches!(pattern, &Pattern::Spread(_)) {
//             has_spread = true;
//         }

//         is_pattern_irrefutable(pattern)
//     });

//     all_children_irrefutable && has_spread
// }
