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

use std::fs;

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
use hash_testing_internal::{metadata::TestResult, TestingInput};
use hash_testing_macros::generate_tests;
use hash_typecheck::TcImpl;
use hash_vm::vm::{Interpreter, InterpreterOptions};
use regex::Regex;

use crate::{ANSI_REGEX, REGENERATE_OUTPUT};

/// This function is used to handle the case of verifying that a parser test was
/// expected to fail. This function verifies that it does fail and that the
/// generated [Report] (which is rendered) matches the recorded `case.stderr`
/// entry within the case.
fn handle_failure_case(
    input: TestingInput,
    diagnostics: Vec<Report>,
    sources: Workspace,
) -> std::io::Result<()> {
    // Verify that the parser failed to parse this file
    assert!(
        diagnostics.iter().any(|report| report.is_error()),
        "parsing file: {:?} did not fail",
        input.path
    );

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
        assert!(diagnostics.is_empty(), "parsing file failed: {:?}", input.path);
    }
}

// Generate all the tests
generate_tests!("./cases/", r"^*\.hash$", "ui", handle_test);
