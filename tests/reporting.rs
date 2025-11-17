//! Test reporting utilities for formatting test errors in a consistent way.

use std::path::Path;

/// Test error information for structured output
#[derive(Debug)]
pub struct TestErrorInfo {
    file_path: String,
    message: String,
    error_type: String,
}

impl TestErrorInfo {
    /// Create a new TestErrorInfo from a test file path, message, and error
    /// type.
    pub fn new(path: &Path, message: impl Into<String>, error_type: impl Into<String>) -> Self {
        let test_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let file_path = test_path.display().to_string();

        Self { file_path, message: message.into(), error_type: error_type.into() }
    }

    /// Format the error message as human-readable text.
    pub fn format(&self) -> String {
        format!(
            "Test Error: {}\nTest case file: {}\n\n{}",
            self.error_type, self.file_path, self.message
        )
    }
}
