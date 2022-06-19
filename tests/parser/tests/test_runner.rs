#![cfg(test)]

use std::fs;

use hash_parser::HashParser;
use hash_pipeline::{
    sources::{Module, Sources},
    traits::Parser,
};
use hash_reporting::reporting::{Report, ReportWriter};
use hash_source::SourceId;
use hash_utils::testing::TestingInput;
use hash_utils_testing_macros::generate_tests;
use lazy_static::lazy_static;
use regex::Regex;

/// Whether or not the UI tests should re-generate the output.
const REGENERATE_OUTPUT: bool = false;

/// This is the ANSI Regular expression matcher. This will match all the specified
/// ANSI escape codes that are used by the [`hash_reporting`] crate.
const ANSI_RE: &str = r"[\x1b\x9b]\[[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-ORZcf-nqry=><]";

lazy_static! {
    pub static ref ANSI_REGEX: Regex = Regex::new(ANSI_RE).unwrap();
}

/// This function is used to handle the case of verifying that a parser test was
/// expected to fail. This function verifies that it does fail and that the
/// generated [Report] (which is rendered) matches the recorded `case.stderr`
/// entry within the case.
fn handle_failure_case(
    input: TestingInput,
    result: Result<(), Vec<Report>>,
    sources: Sources,
) -> std::io::Result<()> {
    let content_path = input.path.join("case.hash");

    // Verify that the parser failed to parse this file
    assert!(
        result.is_err(),
        "parsing file: {:?} did not fail",
        content_path
    );

    let diagnostics = result.unwrap_err();
    let contents = diagnostics
        .into_iter()
        .map(|report| format!("{}", ReportWriter::new(report, &sources)))
        .collect::<Vec<_>>()
        .join("\n");

    // Remove any ANSI escape codes generated from the reporting...
    let report_contents = ANSI_REGEX.replace_all(contents.as_str(), "");

    // Replace the directory by `$DIR`
    let dir_regex = Regex::new(input.path.as_path().to_str().unwrap()).unwrap();
    let report_contents = dir_regex
        .replace_all(report_contents.as_ref(), r"$$DIR")
        .to_string();

    // We want to load the `.stderr` file and verify that the contents of the
    // file match to the created report. If the `.stderr` file does not exist
    // then we create it and write the generated report to that file
    let stderr_path = input.path.join("case.stderr");

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
            "Missing `.stderr` file for `{:?}`. Consider running with `REGENERATE_OUTPUT=true`",
            content_path
        );
    }

    Ok(())
}

/// Generic test handler in the event whether a case should pass or fail.
fn handle_test(input: TestingInput) {
    // determine if this test should fail or not
    let should_fail = input.snake_name.starts_with("should_fail");

    let mut sources = Sources::new();
    let content_path = input.path.join("case.hash");
    let target = Module::new(content_path.clone());
    let target_id = sources.add_module(target);

    let mut parser = HashParser::new();

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .thread_name(|id| format!("parse-worker-{}", id))
        .build()
        .unwrap();

    // Now parse the module and store the result
    let result = parser.parse(SourceId::Module(target_id), &mut sources, &pool);

    if should_fail {
        handle_failure_case(input, result, sources).unwrap();
    } else {
        // Check whether the result fails or not, depending on if the file_path begins with
        // 'should_fail'...
        assert!(result.is_ok(), "parsing file failed: {:?}", content_path);
    }
}
// "case.hash" is the test pattern.
generate_tests!("./cases/", r"^case\.hash$", "self", handle_test);
