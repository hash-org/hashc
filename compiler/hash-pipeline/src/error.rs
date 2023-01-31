//! Defines the error type for the hash pipeline. These errors
//! can originate from the parsing of specified compiler arguments,
//! resolving file paths, or when bootstrapping the compiler pipeline.

use std::{io, path::PathBuf};

use hash_reporting::report::{Report, ReportKind};

use crate::fs::ImportError;

// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug)]
pub enum PipelineError {
    /// Invalid target was passed to the compiler.
    InvalidTarget(String),

    /// Error that can occur when the pipeline tried to
    /// create a resource on the operating system, but the resource
    /// couldn't be created for some reason.
    ResourceCreation {
        /// The item that was being created.
        path: PathBuf,

        /// The specific [io::Error] that occurred.
        error: io::Error,
    },

    /// Errors that can occur from importing module paths
    /// when the compiler settings are still being processed.
    ImportPath(ImportError),

    /// When a specific "stage" of the compiler is specified.
    /// but there exists no such stage.
    UnknownStage(String),

    /// When a stage is specified but the entry point is missing.
    MissingEntryPoint,

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

impl From<PipelineError> for Report {
    fn from(value: PipelineError) -> Self {
        let mut report = Report::new();
        let message = match value {
            PipelineError::InvalidTarget(target) => format!(
                "invalid target `{target}` specified, available targets are: `x86_64` and `x64`"
            ),
            PipelineError::MissingEntryPoint => "missing entry point".to_string(),
            PipelineError::UnknownStage(stage) => format!("unknown stage `{stage}`, available stages are: `ast-gen`, `check`, `ir-gen`, `build`"),
            PipelineError::ResourceCreation { path, error } => {
                let kind = error.kind();

                error.raw_os_error().map_or_else(
                    || format!("couldn't create `{}`, {}", path.to_string_lossy(), kind),
                    |code| format!("couldn't create `{}`, {} (code: {})", path.to_string_lossy(), kind, code),
                )
            },
            PipelineError::ImportPath(err) => err.to_string(),
            PipelineError::UnknownKey(key) => {
                format!("unknown configuration key `{key}`")
            }
            PipelineError::MalformedKey(key) => {
                format!("malformed configuration key `{key}`")
            }
            PipelineError::MissingValue(key) => {
                format!("missing value for configuration key `{key}`")
            }
            PipelineError::InvalidValue(key, value) => {
                format!("invalid value `{value}` for configuration key `{key}`")
            }
        };

        report.kind(ReportKind::Error).title(message);
        report
    }
}
