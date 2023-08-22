//! All diagnostics that are related to exhaustiveness and reachability checking
//! for pattern matching.

use hash_ast::ast::{MatchOrigin, RangeEnd};
use hash_reporting::{
    diagnostic::DiagnosticCellStore, hash_error_codes::error_codes::HashErrorCode,
    reporter::Reporter,
};
use hash_source::location::Span;
use hash_tir::{lits::LitPat, pats::PatId, utils::common::get_location};
use hash_utils::{
    itertools::Itertools,
    pluralise,
    printing::{SequenceDisplay, SequenceDisplayOptions, SequenceJoinMode},
};

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
        location: Span,

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

impl ExhaustivenessError {
    /// Adds the given [ExhaustivenessError] to the report builder.
    pub fn add_to_reports(&self, reporter: &mut Reporter) {
        match self {
            ExhaustivenessError::RefutablePat { pat, origin, uncovered_pats } => {
                let origin = match origin {
                    Some(kind) => match kind {
                        MatchOrigin::Match => "`match`",
                        MatchOrigin::If => "`if`",
                        MatchOrigin::For => "for-loop",
                        MatchOrigin::While => "`while` binding",
                    },
                    None => "declaration",
                };

                // Prepare patterns for printing
                let uncovered = uncovered_pats.iter().map(|pat| format!("{pat}")).collect_vec();
                let pats = SequenceDisplay::new(
                    &uncovered,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 3),
                );

                reporter
                    .error()
                    .code(HashErrorCode::RefutablePat)
                    .title(format!("refutable pattern in {origin} binding: {pats} not covered"))
                    .add_labelled_span(
                        get_location(pat).unwrap(),
                        format!("pattern{} {pats} not covered", pluralise!(uncovered_pats.len())),
                    );
            }
            ExhaustivenessError::NonExhaustiveMatch { location, uncovered_pats } => {
                let uncovered = uncovered_pats.iter().map(|pat| format!("{pat}")).collect_vec();
                let pats = SequenceDisplay::new(
                    &uncovered,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 3),
                );

                reporter
                    .error()
                    .code(HashErrorCode::NonExhaustiveMatch)
                    .title(format!("non-exhaustive patterns: {pats} not covered"))
                    .add_labelled_span(
                        *location,
                        format!("pattern{} {pats} not covered", pluralise!(uncovered_pats.len())),
                    );
            }
            ExhaustivenessError::InvalidRangePatBoundaries { end, pat } => {
                let message = match end {
                    RangeEnd::Included => {
                        "lower range bound must be less than or equal to the upper bound"
                    }
                    RangeEnd::Excluded => "lower range bound must be less than upper bound",
                };

                reporter
                    .error()
                    .code(HashErrorCode::InvalidRangePatBoundaries)
                    .title(message)
                    .add_labelled_span(get_location(pat).unwrap(), "");
            }
        }
    }
}

/// Warnings that can be emitted by the exhaustiveness checker.
#[derive(Debug, Clone)]
pub enum ExhaustivenessWarning {
    /// Given match case is never going to match the subject.
    UselessMatchCase {
        /// The pattern that is considered to be useless.
        pat: PatId,

        /// The location of the match subject that is being checked.
        location: Span,
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

impl ExhaustivenessWarning {
    pub fn add_to_reports(&self, reporter: &mut Reporter) {
        match self {
            ExhaustivenessWarning::UselessMatchCase { pat, location } => {
                reporter
                    .warning()
                    .title(format!("match case `{pat}` is redundant when matching on subject"))
                    .add_labelled_span(*location, "the match subject is given here...")
                    .add_labelled_span(
                        get_location(pat).unwrap(),
                        "... and this pattern will never match the subject",
                    );
            }
            ExhaustivenessWarning::UnreachablePat { pat } => {
                reporter
                    .warning()
                    .title("pattern is unreachable")
                    .add_labelled_span(get_location(pat).unwrap(), "");
            }
            ExhaustivenessWarning::OverlappingRangeEnd { range, overlaps, overlapping_term } => {
                reporter
                    .warning()
                    .title("range pattern has an overlap with another pattern")
                    .add_labelled_span(
                        get_location(range).unwrap(),
                        format!("this range overlaps on `{overlapping_term}`..."),
                    )
                    .add_labelled_span(get_location(overlaps).unwrap(), "...with this range");
            }
        }
    }
}
