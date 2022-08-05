//! Testing utilities for running various tests that might include
//! resources on the disk.
//!
//! See the `hash-utils-testing-macros` crate for more information.
use std::path::PathBuf;

/// Represents the input to a test, which is the path to the test input and a
/// snake case name.
#[derive(Debug, Clone)]
pub struct TestingInput {
    pub path: PathBuf,
    pub snake_name: String,
}

/// A function that takes in a [TestingInput].
pub type TestingFn = fn(input: TestingInput);
