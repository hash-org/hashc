//! A diagnostic reporter for the Hash compiler.
//!
//! Has a fluent API for creating reports in a declarative way.
use std::fmt;

use crate::report::{Report, ReportKind};
pub type Reports = Vec<Report>;

/// Facilitates the creation of lists of [Report]s in a declarative way.
#[derive(Debug, Default)]
pub struct Reporter {
    reports: Vec<Report>,
}

impl Reporter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a report to the builder.
    pub fn report(&mut self, kind: ReportKind) -> &mut Report {
        let mut report = Report::new();
        report.kind(kind);
        self.reports.push(report);
        self.reports.last_mut().unwrap()
    }

    /// Create a new reporter from a list of reports.
    pub fn from_reports(reports: Vec<Report>) -> Self {
        Self { reports }
    }

    /// Add an error report to the builder.
    pub fn error(&mut self) -> &mut Report {
        self.report(ReportKind::Error)
    }

    /// Add an info report to the builder.
    pub fn info(&mut self) -> &mut Report {
        self.report(ReportKind::Info)
    }

    /// Add a warning report to the builder.
    pub fn warning(&mut self) -> &mut Report {
        self.report(ReportKind::Warning)
    }

    /// Add an internal report to the builder.
    pub fn internal(&mut self) -> &mut Report {
        self.report(ReportKind::Internal)
    }

    /// Consume the [`Reporter`], producing a [`Vec<Report>`].
    pub fn into_reports(self) -> Reports {
        self.reports
    }
}

/// A trait for adding a diagnostic to a reporter.
pub trait AddToReporter {
    fn add_to_reporter(&self, reporter: &mut Reporter);
}

impl fmt::Display for Reporter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for report in &self.reports {
            write!(f, "{report}")?;
        }
        Ok(())
    }
}
