//! Hash Compiler UI Test runner, this file will read the `cases` directory for
//! `.hash` files in the specific `should_pass` and `should_fail` directories.
//!
//! In the event of a `should_pass` case, the resultant run should not return
//! any errors. However, it's possible for the case to generate warnings
//! (which is not currently tested).
//!
//! In the event of a `should_fail` case, the test will emit "reports" that
//! signal what the error is, the case handler will render the reports
//! into strings, strip any kind of ANSI codes, and compare with the
//! `case.stderr` to ensure that the test produces the expected errors.
//!
//! Additionally, it's also possible for the case file to specify at the
//! top of the file what testing parameters should be provided, for example
//!
//!
//! If the case is in `should_fail`:
//! ```ignore
//! // stage-parse, pass
//!
//! foo := () => { ... };
//!
//! bar := () => { ... };
//! ```
//!
//! In this example, the case specifies that the stage should only go up to the
//! "parsing" stage and then stop compiling, and emit the errors.
#![cfg(test)]

use std::{fs, path::PathBuf};

use hash_parser::HashParser;
use hash_pipeline::{
    fs::read_in_path,
    sources::{Module, Workspace},
    traits::Parser,
};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_source::{ModuleKind, SourceId};
use hash_testing_macros::generate_tests;
use regex::Regex;

use crate::{ANSI_REGEX, REGENERATE_OUTPUT};

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

    /// Generated snake-cae name for the file
    ///
    /// @@Deprecated
    pub snake_name: String,
}

/// This function is used to handle the case of verifying that a parser test was
/// expected to fail. This function verifies that it does fail and that the
/// generated [Report] (which is rendered) matches the recorded `case.stderr`
/// entry within the case.
fn handle_failure_case(
    input: TestingInput,
    result: Result<(), Vec<Report>>,
    sources: Workspace,
) -> std::io::Result<()> {
    // Verify that the parser failed to parse this file
    assert!(result.is_err(), "parsing file: {:?} did not fail", input.path);

    let diagnostics = result.unwrap_err();
    let contents = diagnostics
        .into_iter()
        .map(|report| format!("{}", ReportWriter::new(report, sources.source_map())))
        .collect::<Vec<_>>()
        .join("\n");

    let test_dir = input.path.parent().unwrap();

    // Remove any ANSI escape codes generated from the reporting...
    let report_contents = ANSI_REGEX.replace_all(contents.as_str(), "");

    // Replace the directory by `$DIR`
    let dir_regex = Regex::new(test_dir.to_str().unwrap()).unwrap();
    let report_contents = dir_regex.replace_all(report_contents.as_ref(), r"$$DIR").to_string();

    // We want to load the `.stderr` file and verify that the contents of the
    // file match to the created report. If the `.stderr` file does not exist
    // then we create it and write the generated report to that file
    let stderr_path = test_dir.join(format!("{}.stderr", input.filename));

    // If we specify to re-generate the output, then we will always write the
    // content of the report into the specified file
    if REGENERATE_OUTPUT || !stderr_path.exists() {
        fs::write(&stderr_path, &report_contents)?;
    }

    if stderr_path.exists() {
        let err_contents = fs::read_to_string(stderr_path).unwrap();

        pretty_assertions::assert_eq!(err_contents, report_contents);
    } else {
        panic!(
            "missing `.stderr` file for `{:?}`, consider running with `REGENERATE_OUTPUT=true`",
            input.path
        );
    }

    Ok(())
}

/// Generic test handler in the event whether a case should pass or fail.
fn handle_test(input: TestingInput) {
    // determine if this test should fail or not
    let should_fail = input.snake_name.starts_with("should_fail");

    let mut workspace = Workspace::new();
    let target = Module::new(input.path.clone());
    let contents = read_in_path(input.path.as_path()).unwrap();

    let target_id = workspace.add_module(contents, target, ModuleKind::Normal);

    let mut parser = HashParser::new();

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .thread_name(|id| format!("parse-worker-{}", id))
        .build()
        .unwrap();

    // Now parse the module and store the result
    let result = parser.parse(SourceId::Module(target_id), &mut workspace, &pool);

    if should_fail {
        handle_failure_case(input, result, workspace).unwrap();
    } else {
        // Check whether the result fails or not, depending on if the file_path begins
        // with 'should_fail'...
        assert!(result.is_ok(), "parsing file failed: {:?}", input.path);
    }
}

// Generate all the tests
generate_tests!("./cases/", r"^*\.hash$", "ui", handle_test);
