//! All errors that can occur whilst generating code using the
//! LLVM backend.

use hash_reporting::report::{Report, ReportKind};
use inkwell::support::LLVMString;

pub type CodegenResult<T> = Result<T, CodeGenError>;

/// Errors that can occur during code generation.
pub enum CodeGenError {
    /// When module verification fails.
    ModuleVerificationFailed {
        /// The reason for the failure.
        reason: LLVMString,
    },

    /// When writing a module to disk fails.
    ModuleWriteFailed {
        /// The reason for the failure.
        reason: LLVMString,
    },
}

impl From<CodeGenError> for Report {
    fn from(error: CodeGenError) -> Self {
        let mut report = Report::new();

        match error {
            CodeGenError::ModuleVerificationFailed { reason } => {
                report.kind(ReportKind::Internal).title("LLVM Module verification Error");

                for line in reason.to_string().lines() {
                    report.add_info(line);
                }
            }
            CodeGenError::ModuleWriteFailed { reason } => {
                report.kind(ReportKind::Error).title("failed to write object file to disk");

                for line in reason.to_string().lines() {
                    report.add_info(line);
                }
            }
        };

        report
    }
}
