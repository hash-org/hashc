//! Hash Compiler pipeline errors that can occur during the
//! the pipeline initialisation.
use std::{fmt, io};

use hash_reporting::report::{Report, ReportKind};

#[derive(Debug)]
pub enum ArgumentError {
    /// When a configuration key is not recognised.
    UnknownKey(String),

    /// When a key-value pair doesn't follow the standard
    /// `-C<key>=<value>` format.
    MalformedKey(String),

    /// A key was provided but was missing a key.
    MissingValue(String),

    /// When a configuration key value is not a valid option
    /// for the specified key.
    InvalidValue(String, String),
}

impl From<ArgumentError> for CompilerError {
    fn from(err: ArgumentError) -> Self {
        CompilerError::Argument(err)
    }
}

impl fmt::Display for ArgumentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            ArgumentError::UnknownKey(key) => {
                format!("unknown configuration key `{key}`")
            }
            ArgumentError::MalformedKey(key) => {
                format!("malformed configuration key `{key}`")
            }
            ArgumentError::MissingValue(key) => {
                format!("missing value for configuration key `{key}`")
            }
            ArgumentError::InvalidValue(key, value) => {
                format!("invalid value `{value}` for configuration key `{key}`")
            }
        };

        write!(f, "{message}")
    }
}

/// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug)]
pub enum CompilerError {
    /// Invalid target was passed to the compiler.
    InvalidTarget(String),

    /// Generic IO error.
    Io(io::Error),

    /// When a specific "stage" of the compiler is specified.
    /// but there exists no such stage.
    UnknownStage(String),

    /// When a stage is specified but the entry point is missing.
    MissingEntryPoint,

    /// Error when arguments to a particular command occur.
    Argument(ArgumentError),
}

impl From<CompilerError> for Report {
    fn from(value: CompilerError) -> Self {
        let mut report = Report::new();
        let message = match value {
            CompilerError::InvalidTarget(target) => format!(
                "invalid target `{target}` specified, available targets are: `x86_64` and `x64`"
            ),
            CompilerError::MissingEntryPoint => "missing entry point".to_string(),
            CompilerError::UnknownStage(stage) => format!("unknown stage `{stage}`, available stages are: `ast-gen`, `check`, `ir-gen`, `build`"),
            CompilerError::Io(err) => err.to_string(),
            CompilerError::Argument(err) => err.to_string(),
        };

        report.kind(ReportKind::Error).title(message);
        report
    }
}
