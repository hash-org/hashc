//! Hash typechecking warning data structures and implementation.
//! Warnings within the typechecker are essentially generated and
//! are meant as a guide for the user when compiling programs. These
//! warnings do not affect the resultant output of the program, and
//! are never fatal to the compilation stage.
//!
//! @@Future: In the future, it should be possible to have a general
//! corpus of all the warnings that the compiler could emit, and support
//! for configuring if those warnings should be emitted for a given
//! job.

use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind},
};

use crate::{
    fmt::PrepareForFormatting,
    storage::{pats::PatId, terms::TermId, AccessToStorage, StorageRef},
};

/// A warning that occurs during typechecking.
#[derive(Debug, Clone)]
pub enum TcWarning {
    /// Given match case is never going to match the subject.
    UselessMatchCase {
        pat: PatId,
        subject: TermId,
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
        overlapping_term: TermId,
    },
}

/// A [TcWarning] with attached typechecker storage.
pub(crate) struct TcWarningWithStorage<'tc> {
    pub warning: TcWarning,
    pub storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for TcWarningWithStorage<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> From<TcWarningWithStorage<'tc>> for Report {
    fn from(item: TcWarningWithStorage<'tc>) -> Self {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Warning);

        match item.warning {
            TcWarning::UselessMatchCase { pat, subject } => {
                builder.with_message(format!(
                    "match case `{}` is redundant when matching on `{}`",
                    pat.for_formatting(item.global_storage()),
                    subject.for_formatting(item.global_storage())
                ));

                if let Some(location) = item.location_store().get_location(subject) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "the match subject is given here...",
                    )));
                }

                if let Some(location) = item.location_store().get_location(pat) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "...and this pattern will never match the subject".to_string(),
                    )));
                }
            }
            TcWarning::UnreachablePat { pat } => {
                builder.with_message("pattern is unreachable".to_string());

                if let Some(location) = item.location_store().get_location(pat) {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")));
                }
            }
            TcWarning::OverlappingRangeEnd { range, overlapping_term, overlaps } => {
                builder.with_message("range pattern has an overlap with another pattern");

                if let Some(location) = item.location_store().get_location(range) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "this range overlaps on `{}`...",
                            overlapping_term.for_formatting(item.global_storage())
                        ),
                    )));
                }

                if let Some(location) = item.location_store().get_location(overlaps) {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "...with this range",
                    )));
                }
            }
        }

        builder.build()
    }
}
