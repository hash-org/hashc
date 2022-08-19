//! Hash Compiler UI Test runner, this file will read the `cases` directory for
//! `.hash` files.
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
//! top of the file what testing parameters should be provided, for example:
//! ```ignore
//! // stage=parse, run=fail
//!
//! foo := () => { ... };
//!
//! bar := () => { ... };
//! ```
//!
//! In this example, the case specifies that the stage should only go up to the
//! "parsing" stage and then stop compiling, and that the test case should fail.
#![cfg(test)]

use std::{fs, io};

use hash_ast_desugaring::AstDesugarer;
use hash_ast_passes::HashSemanticAnalysis;
use hash_parser::HashParser;
use hash_pipeline::{
    settings::{CompilerJobParams, CompilerSettings},
    sources::Workspace,
    Compiler,
};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_source::ModuleKind;
use hash_testing_internal::{
    metadata::{HandleWarnings, TestResult},
    TestingInput,
};
use hash_testing_macros::generate_tests;
use hash_typecheck::TcImpl;
use hash_vm::vm::{Interpreter, InterpreterOptions};
use regex::Regex;

use crate::{ANSI_REGEX, REGENERATE_OUTPUT};

/// Given the testing input, and a pre-filtered [Vec<Report>] based on
/// the testing input parameters, render the reports and compare them
/// to the saved corresponding `.stderr` file.
///
/// The report comparison removes all ANSI escape codes, and directory paths.
fn compare_emitted_diagnostics(
    input: TestingInput,
    diagnostics: Vec<Report>,
    sources: Workspace,
) -> std::io::Result<()> {
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
        // Avoid writing nothing to the `.stderr` case file
        if !report_contents.is_empty() {
            fs::write(&stderr_path, &report_contents)?;
        }
    }

    // Read the contents of the file, if we couldn't find the file then we assume
    // that the contents of `.stderr` are empty. We can assume this because the
    // only reason why the file wouldn't be written to is if it didn't exist
    // prior to this and that the contents of the diagnostics are empty, so
    // returning an empty string makes sense here.
    let err_contents =
        fs::read_to_string(stderr_path.clone()).unwrap_or_else(|err| match err.kind() {
            io::ErrorKind::NotFound => "".to_string(),
            err => panic!("couldn't open file `{stderr_path:?}`: {:?}", err),
        });

    pretty_assertions::assert_str_eq!(
        err_contents,
        report_contents,
        "\ncase `.stderr` does not match for: {:#?}\n",
        input
    );

    Ok(())
}

/// This function is used to handle the case of verifying that a parser test was
/// expected to fail. This function verifies that it does fail and that the
/// generated [Report] (which is rendered) matches the recorded `case.stderr`
/// entry within the case.
///
/// If the case specifies that `warnings=ignore`, then warnings will not be
/// considered within the resultant `.stderr` file.
fn handle_failure_case(
    input: TestingInput,
    diagnostics: Vec<Report>,
    sources: Workspace,
) -> std::io::Result<()> {
    // verify that the case failed, as in reports where generated
    assert!(
        diagnostics.iter().any(|report| report.is_error()),
        "\ntest case did not fail: {:#?}",
        input
    );

    // If the test specifies that no warnings should be generated, then check
    // that this is the case
    if input.metadata.warnings == HandleWarnings::Disallow {
        assert!(
            diagnostics.iter().all(|report| report.is_error()),
            "\ntest case generated warnings where they were disallowed: {:#?}",
            input
        );
    }

    // Filter out `warnings` if the function specifies them to be
    // ignored.
    let diagnostics = diagnostics
        .into_iter()
        .filter(|report| {
            if input.metadata.warnings == HandleWarnings::Ignore {
                report.is_error()
            } else {
                true
            }
        })
        .collect();

    compare_emitted_diagnostics(input, diagnostics, sources)
}

/// Function that handles a test case which is expected to be successful, in
/// this situation, the function will verify that the test case did not emit any
/// errors or warnings (although setting `warnings=ignore` will ignore
/// warnings).
fn handle_pass_case(
    input: TestingInput,
    diagnostics: Vec<Report>,
    sources: Workspace,
) -> std::io::Result<()> {
    let did_pass = match input.metadata.warnings {
        HandleWarnings::Ignore | HandleWarnings::Compare => {
            diagnostics.iter().all(|report| report.is_warning())
        }
        // Expect no diagnostics to be emitted whatsoever
        HandleWarnings::Disallow => diagnostics.is_empty(),
    };

    if !did_pass {
        panic!(
            "\ntest case did not pass:\n{}",
            diagnostics
                .into_iter()
                .map(|report| format!("{}", ReportWriter::new(report, sources.source_map())))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    // If we need to compare the output of the warnings, to the previous result...
    if input.metadata.warnings == HandleWarnings::Compare {
        compare_emitted_diagnostics(input, diagnostics, sources)?;
    }

    Ok(())
}

/// Generic test handler in the event whether a case should pass or fail.
fn handle_test(input: TestingInput) {
    // Initialise the compiler pipeline
    let parser = HashParser::new();
    let desugarer = AstDesugarer;
    let semantic_analyser = HashSemanticAnalysis;
    let checker = TcImpl;

    // Create the vm
    let vm = Interpreter::new(InterpreterOptions::default());

    let worker_count = 2;
    let mut compiler_settings = CompilerSettings::new(false, worker_count);
    compiler_settings.set_skip_prelude(true);
    compiler_settings.set_emit_errors(false);

    // We need at least 2 workers for the parsing loop in order so that the job
    // queue can run within a worker and any other jobs can run inside another
    // worker or workers.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count)
        .thread_name(|id| format!("compiler-worker-{}", id))
        .build()
        .unwrap();

    let mut compiler =
        Compiler::new(parser, desugarer, semantic_analyser, checker, vm, &pool, compiler_settings);
    let mut compiler_state = compiler.bootstrap();

    // // Now parse the module and store the result
    compiler_state = compiler.run_on_filename(
        input.path.to_str().unwrap(),
        ModuleKind::Normal,
        compiler_state,
        CompilerJobParams::new(input.metadata.stage, false),
    );

    let diagnostics = compiler_state.diagnostics;

    // Based on the specified metadata within the test case itself, we know
    // whether the test should fail or not
    if input.metadata.completion == TestResult::Fail {
        handle_failure_case(input, diagnostics, compiler_state.workspace).unwrap();
    } else {
        handle_pass_case(input, diagnostics, compiler_state.workspace).unwrap();
    }
}

// Generate all the tests
generate_tests!("./cases/", r"^*\.hash$", "ui", handle_test);
