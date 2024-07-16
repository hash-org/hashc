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
    ParseError(clap::Error),

    /// Error that can occur when the pipeline tried to
    /// create a resource on the operating system, but the resource
    /// couldn't be created for some reason.
    ResourceCreation {
        /// The item that was being created.
        path: PathBuf,

        /// The specific [io::Error] that occurred.
        error: io::Error,
    },

    /// The requested pipeline configuration expected an entrypoint.
    MissingEntryPoint,

    /// Errors that can occur from importing module paths
    /// when the compiler settings are still being processed.
    ImportPath(ImportError),

    /// When a configuration key value is not a valid option
    /// for the specified key.
    InvalidValue(String, String),
}

impl From<PipelineError> for Report {
    fn from(value: PipelineError) -> Self {
        let mut report = Report::new();
        let message = match value {
            PipelineError::ParseError(err) => err.to_string(),

            PipelineError::ResourceCreation { path, error } => {
                let kind = error.kind();

                error.raw_os_error().map_or_else(
                    || format!("couldn't create `{}`, {}", path.to_string_lossy(), kind),
                    |code| {
                        format!(
                            "couldn't create `{}`, {} (code: {})",
                            path.to_string_lossy(),
                            kind,
                            code
                        )
                    },
                )
            }
            PipelineError::MissingEntryPoint => "no entry point was specified".to_string(),
            PipelineError::ImportPath(err) => err.to_string(),
            PipelineError::InvalidValue(key, value) => {
                format!("invalid value `{value}` for configuration key `{key}`")
            }
        };

        report.kind(ReportKind::Error).title(message);
        report
    }
}
