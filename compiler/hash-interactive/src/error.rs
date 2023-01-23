//! Represents all of the errors that occur when running within the
//! Hash REPL.

use hash_reporting::report::{Report, ReportKind};

pub type InteractiveResult<T> = Result<T, InteractiveError>;

/// Enum representing the variants of error that can occur when running an
/// interactive session
#[derive(Debug)]
pub enum InteractiveError {
    /// Encountering an unknown command.
    UnrecognisedCommand(String),

    /// When a command received arguments it wasn't expecting.
    UnexpectedArgument(String),

    /// When a command didn't receive the correct number of arguments.
    MissingOperand(String),

    /// An unknown error occurred.
    Internal(String),
}

impl From<InteractiveError> for Report {
    fn from(error: InteractiveError) -> Self {
        let mut report = Report::new();

        match error {
            InteractiveError::UnrecognisedCommand(command) => {
                report.kind(ReportKind::Error).title(format!("unrecognised command `{command}`"))
            }
            InteractiveError::UnexpectedArgument(arg) => report
                .kind(ReportKind::Error)
                .title(format!("unexpected argument `{arg}` for command")),
            InteractiveError::MissingOperand(arg) => {
                report.kind(ReportKind::Error).title(format!("missing operand for `{arg}`"))
            }
            InteractiveError::Internal(message) => report.kind(ReportKind::Internal).title(message),
        };

        report
    }
}
