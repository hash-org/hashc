//! Contains logic for parsing test case configurations into
//! a readable format for the test runner to interpret adjust
//! it's behaviour.
#![feature(iter_advance_by)]
pub mod metadata;

use std::path::PathBuf;

use metadata::TestMetadata;

/// Represents the input to a test, which is the path to the test input and a
/// snake case name.
#[derive(Debug, Clone)]
pub struct TestingInput {
    /// The path to the test file
    pub path: PathBuf,
    /// filename of the test, useful for when looking for resources
    /// that have been generated that are related to the file.
    ///
    /// N.B. the `filename` does not contain `.hash` prefix.
    pub filename: String,

    /// Generated test metadata for the case
    pub metadata: TestMetadata,
}
