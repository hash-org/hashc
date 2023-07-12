//! All diagnostics that are related to exhaustiveness and reachability checking
//! for pattern matching.

use hash_ast::ast::{MatchOrigin, RangeEnd};
use hash_reporting::diagnostic::DiagnosticCellStore;
use hash_source::location::SourceLocation;
use hash_tir::{lits::LitPat, pats::PatId};

pub type ExhaustivenessDiagnostics =
    DiagnosticCellStore<ExhaustivenessError, ExhaustivenessWarning>;

/// All of the errors and warnings that can be emitted by the exhaustiveness
/// checker.
pub enum ExhaustivenessDiagnostic {
    /// Warnings that are emitted by the exhaustiveness.
    Warning(ExhaustivenessWarning),

    /// Errors that are emitted by the exhaustiveness.
    Error(ExhaustivenessError),
}

/// Errors that can be emitted during exhaustiveness checking.
#[derive(Debug, Clone)]
pub enum ExhaustivenessError {
    /// When a pattern is expected to be irrefutable but was found to be
    /// refutable with provided `witnesses` or possible patterns that are
    /// not covered by the pattern.
    RefutablePat {
        /// The pattern that is refutable
        pat: PatId,

        /// Where the refutability check came from, `for`, `while`, `match`...
        ///
        /// Although we should only really ever get `for` or `None` which means
        /// it's either in a for-loop or a declaration.
        origin: Option<MatchOrigin>,

        /// Generated patterns that are not covered by `pat`
        uncovered_pats: Vec<PatId>,
    },
    /// When a match block is non-exhaustive
    NonExhaustiveMatch {
        /// The term of the subject expression.
        location: SourceLocation,

        /// Generated patterns that are not covered by match arms
        uncovered_pats: Vec<PatId>,
    },
    /// When an inclusive range pattern boundaries are invalid
    InvalidRangePatBoundaries {
        /// The kind of range end this pattern has,
        end: RangeEnd,

        /// The ID of the pattern that is invalid.
        pat: PatId,
    },
}

/// Warnings that can be emitted by the exhaustiveness checker.
#[derive(Debug, Clone)]
pub enum ExhaustivenessWarning {
    /// Given match case is never going to match the subject.
    UselessMatchCase {
        /// The pattern that is considered to be useless.
        pat: PatId,

        /// The location of the match subject that is being checked.
        location: SourceLocation,
    },

    // Exhaustiveness checking has found this pattern to
    // be unreachable in the current context. In other words, the branch
    // that the pattern corresponds to will never be reached because it
    // is always caught by a predecessing pattern.
    UnreachablePat {
        pat: PatId,
    },

    /// When one ranges end is overlapping with another range
    /// end, this warning does not cover general overlapping ranges.
    OverlappingRangeEnd {
        /// This range's end is overlapping with another range start
        range: PatId,

        /// This is the range start that the `range` is overlapping with
        overlaps: PatId,

        /// The specific term that is overlapping between the two ranges.
        overlapping_term: LitPat,
    },
}
