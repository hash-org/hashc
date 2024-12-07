//! Defines the error type for the hash pipeline. These errors
//! can originate from the parsing of specified compiler arguments,
//! resolving file paths, or when bootstrapping the compiler pipeline.

use std::{io, path::PathBuf};

use clap::error::ErrorKind;
use hash_reporting::report::{Report, ReportKind};

use crate::fs::ImportError;

// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug)]
pub enum PipelineError {
    /// Some parsing error that clap emits, it could be benign.
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

        match value {
            PipelineError::ParseError(error) => {
                match error.kind() {
                    ErrorKind::DisplayHelp
                    | ErrorKind::DisplayVersion
                    | ErrorKind::DisplayHelpOnMissingArgumentOrSubcommand => {
                        report.kind(ReportKind::Info);
                    }
                    _ => {
                        report.kind(ReportKind::Error);
                    }
                }

                report.title(error.to_string());
            }

            PipelineError::ResourceCreation { path, error } => {
                let kind = error.kind();

                let message = error.raw_os_error().map_or_else(
                    || format!("couldn't create `{}`, {}", path.to_string_lossy(), kind),
                    |code| {
                        format!(
                            "couldn't create `{}`, {} (code: {})",
                            path.to_string_lossy(),
                            kind,
                            code
                        )
                    },
                );

                report.kind(ReportKind::Error).title(message);
            }
            PipelineError::MissingEntryPoint => {
                report.kind(ReportKind::Error).title("no entry point was specified");
            }
            PipelineError::ImportPath(err) => {
                report.kind(ReportKind::Error).title(err.to_string());
            }
            PipelineError::InvalidValue(key, value) => {
                report
                    .kind(ReportKind::Error)
                    .title(format!("invalid value `{value}` for configuration key `{key}`"));
            }
        };

        report
    }
}
