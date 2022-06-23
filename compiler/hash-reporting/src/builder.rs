//! Hash compiler diagnostic report builder.
use crate::report::{Report, ReportElement, ReportKind};
use hash_error_codes::error_codes::HashErrorCode;

/// A utility struct that allows for a [Report] to be built incrementally
/// adding annotations and other metadata to the report.
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
    pub fn with_message(&mut self, message: impl ToString) -> &mut Self {
        self.message = Some(message.to_string());
        self
    }

    /// Add a general kind to the [Report].
    pub fn with_kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = Some(kind);
        self
    }

    /// Add an associated [HashErrorCode] to the [Report].
    pub fn with_error_code(&mut self, error_code: HashErrorCode) -> &mut Self {
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
