use core::fmt;

use hash_ast::{location::SourceLocation, module::Modules};

use crate::highlight::{Colour, Modifier, highlight};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ErrorCode {
    Parsing,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    Error,
    Info,
    Warning,
}

impl fmt::Display for ReportKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ReportKind::Error => highlight(Colour::Red | Modifier::Bold, "error"),
                ReportKind::Info => highlight(Colour::Blue | Modifier::Bold, "info"),
                ReportKind::Warning => highlight(Colour::Yellow | Modifier::Bold, "warn"),
            }
        )
    }
}

#[derive(Debug)]
pub struct ReportNote {
    pub label: String,
    pub message: String,
}

impl ReportNote {
    pub fn new(label: impl ToString, message: impl ToString) -> Self {
        Self {
            label: label.to_string(),
            message: message.to_string(),
        }
    }
}

#[derive(Debug)]
pub struct Report {
    pub kind: ReportKind,
    pub message: String,
    pub error_code: ErrorCode,

    pub location: SourceLocation,
    pub code_message: String,

    pub additional_notes: Vec<ReportNote>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct IncompleteReportError;

impl std::error::Error for IncompleteReportError {}
impl fmt::Display for IncompleteReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "incomplete report, cannot build")
    }
}

#[derive(Debug, Default)]
pub struct ReportBuilder {
    kind: Option<ReportKind>,
    message: Option<String>,
    error_code: Option<ErrorCode>,
    location: Option<SourceLocation>,
    code_message: Option<String>,
    additional_notes: Vec<ReportNote>,
}

impl ReportBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_message(&mut self, message: impl ToString) -> &mut Self {
        self.message = Some(message.to_string());
        self
    }

    pub fn with_kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = Some(kind);
        self
    }

    pub fn with_error_code(&mut self, error_code: ErrorCode) -> &mut Self {
        self.error_code = Some(error_code);
        self
    }

    pub fn with_location(&mut self, location: SourceLocation) -> &mut Self {
        self.location = Some(location);
        self
    }

    pub fn with_code_message(&mut self, code_message: impl ToString) -> &mut Self {
        self.code_message = Some(code_message.to_string());
        self
    }

    pub fn add_node(&mut self, note: ReportNote) -> &mut Self {
        self.additional_notes.push(note);
        self
    }

    pub fn build(self) -> Result<Report, IncompleteReportError> {
        Ok(Report {
            kind: self.kind.ok_or(IncompleteReportError)?,
            message: self.message.ok_or(IncompleteReportError)?,
            error_code: self.error_code.ok_or(IncompleteReportError)?,
            location: self.location.ok_or(IncompleteReportError)?,
            code_message: self.code_message.ok_or(IncompleteReportError)?,
            additional_notes: self.additional_notes,
        })
    }
}

pub struct ReportWriter<'c, 'm> {
    report: Report,
    modules: &'m Modules<'c>,
}

impl fmt::Display for ReportWriter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.report.kind, self.report.message)?;

        // Print line numbers, separator, then the code itself, split by newlines
        // Should put the code_message where it is supposed to be with a caret (^) followed by (_)
        // or equivalent unicode character.
        //
        // Print a few lines before and after location/code_message.
        write!(f, "{:?}\n{}", self.report.location, self.report.code_message)?;

        write!(f, "{:?}", self.report.location)?;

        Ok(())
    }
}
