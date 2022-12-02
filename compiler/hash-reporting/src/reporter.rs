//! Hash compiler diagnostic report builder.
use hash_error_codes::error_codes::HashErrorCode;

use crate::report::{Report, ReportElement, ReportKind};

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

/// A utility struct that allows for a [Report] to be built incrementally
/// adding annotations and other metadata to the report.
#[deprecated]
#[derive(Debug, Default)]
pub struct ReportBuilder {
    kind: Option<ReportKind>,
    message: Option<String>,
    error_code: Option<HashErrorCode>,
    contents: Vec<ReportElement>,
}

impl ReportBuilder {
    /// Initialise a new [ReportBuilder].
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a general message to the [Report].
    pub fn message(&mut self, message: impl ToString) -> &mut Self {
        self.message = Some(message.to_string());
        self
    }

    /// Add a general kind to the [Report].
    pub fn with_kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = Some(kind);
        self
    }

    /// Add an associated [HashErrorCode] to the [Report].
    pub fn code(&mut self, error_code: HashErrorCode) -> &mut Self {
        self.error_code = Some(error_code);
        self
    }

    /// Add a [ReportElement] to the report.
    pub fn add_element(&mut self, element: ReportElement) -> &mut Self {
        self.contents.push(element);
        self
    }

    /// Create a [Report] from the [ReportBuilder].
    pub fn build(&mut self) -> Report {
        Report {
            kind: self.kind.take().unwrap(),
            message: self.message.take().unwrap(),
            error_code: self.error_code.take(),
            contents: std::mem::take(&mut self.contents),
        }
    }
}
