//! Any errors that occur during the linking procedure
//! of a backend. These errors originate from the linker
//! itself, and are not from the Hash Compiler. We wrap
//! some of the errors from the linker in order to provide
//! more context to the user, and to standardise the error
//! handling across the entire compiler.

use std::{
    path::PathBuf,
    process::{Command, ExitStatus},
    str,
};

use hash_reporting::report::{Report, ReportKind};
use hash_target::TargetArch;

pub type LinkerResult<'a, T> = Result<T, LinkerError<'a>>;

/// Errors that can occur during the configuration of the linker or during
/// the linking process. Some of the errors that can occur are target specific,
/// but it is easier to hold all of the linker errors in one place.
pub enum LinkerError<'a> {
    /// When the linker command was not found on the system.
    NotFound { path: PathBuf },

    /// When a target architecture is not supported for the specified
    /// target CPU.
    UnsupportedArch { arch: TargetArch, os: &'a str },

    /// When the Apple SDK root could not be found.
    AppleSdkRootError { name: &'a str, error: std::io::Error },

    /// The linking process failed with the linker program returning
    /// information about why the linking failed.
    LinkingFailed {
        /// The path to the linker.
        linker_path: &'a PathBuf,

        /// The `exit_status` of the linker program.
        exit_status: ExitStatus,

        /// The command that was used to invoke the linker.
        command: &'a Command,

        /// What the linker program emitted into `stdout` and `stderr`
        escaped_output: &'a str,

        /// The additional information is currently only supported for
        /// `link.exe` since it provides more information about why the
        /// process failed.
        ///
        /// @@Todo: if we have more error handling for other platforms, it would
        /// be nice to make this somehow platform agnostic...
        additional_info: Option<AdditionalFailureInfo>,
    },
}

/// Additional information about why the linking process failed, specific
/// to Windows.
pub struct AdditionalFailureInfo {
    /// Whether an installed version of Visual Studio was found on the
    /// machine.
    pub(crate) is_vs_installed: bool,

    /// Whether `link.exe` was found on the machine.
    pub(crate) has_linker: bool,
}

impl From<LinkerError<'_>> for Report {
    fn from(error: LinkerError<'_>) -> Self {
        let mut report = Report::new();

        let title = match error {
            LinkerError::NotFound { path } => format!("linker `{}` not found", path.display()),
            LinkerError::UnsupportedArch { arch, os } => {
                format!("unsupported architecture `{arch}` for `{os}`")
            }
            LinkerError::AppleSdkRootError { name, error } => {
                format!("could not find Apple SDK `{name}`: {error}")
            }
            LinkerError::LinkingFailed {
                linker_path,
                exit_status,
                command,
                escaped_output,
                additional_info,
            } => {
                // Add the note about command was being run, and the output
                report.add_note(format!("link command:\n{command:?}"));
                report.add_note(escaped_output.to_string());

                // If there is additional information, add notes about this too...
                if let Some(AdditionalFailureInfo { is_vs_installed, has_linker }) = additional_info
                {
                    report.add_info("`link.exe` returned an unexpected error");

                    if is_vs_installed && !has_linker {
                        report.add_note(
                            "the Visual Studio build tools may need to be repaired using the Visual Studio installer \
                            or a necessary component may be missing from the \"C++ build tools\" workload",
                        );
                    } else if is_vs_installed {
                        report.add_note(
                            "no version of `link.exe` was found on the machine, \
                            please install Visual Studio 2019 or later",
                        );
                    } else {
                        report.add_note(
                            "no version of Visual Studio was found on the machine, \
                            please install Visual Studio 2019 or later",
                        );
                    }
                }

                format!("linking with `{linker_path:?}` failed with: {exit_status}")
            }
        };

        report.kind(ReportKind::Error).title(title);
        report
    }
}

/// Utility to convert a returned byte buffer from
/// a [Linker] execution and escape it into a string.
pub fn escape_returned_error(buffer: &[u8]) -> String {
    match str::from_utf8(buffer) {
        Ok(string) => string.to_owned(),
        Err(_) => format!("non-utf8: `{}`", buffer.escape_ascii()),
    }
}
