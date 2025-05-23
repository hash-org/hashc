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

use std::{
    fs, io,
    path::Path,
    sync::{Arc, Mutex},
};

use clap::Parser;
use hash_driver::{Compiler, CompilerBuilder};
use hash_pipeline::{interface::CompilerInterface, settings::CompilerSettings};
use hash_reporting::report::Report;
use hash_testing_internal::{
    TestingInput,
    metadata::{HandleWarnings, TestResult},
};
use hash_testing_macros::generate_tests;
use hash_utils::{
    log,
    logging::{CompilerLogger, CompilerMessagingFormat},
    path::adjust_canonicalisation,
    stream::CompilerOutputStream,
};
use regex::Regex;

use crate::{ANSI_REGEX, REGENERATE_OUTPUT};

const WORKER_COUNT: usize = 2;

/// Convert a [Path] into a [String] whilst also escaping any special
/// characters that may be present in the path. This is useful for when
/// the test-suite runs on Windows, as the path may contain backslashes
/// which are interpreted as escape characters.
fn stringify_test_dir_path(path: &Path) -> String {
    // On windows, the backslashes are special characters, therefore we need
    // to escape them.
    #[cfg(target_os = "windows")]
    let test_dir = {
        let mut dir = regex::escape(&adjust_canonicalisation(path).display().to_string());

        // @@Hack: on windows, the separator is a backslash, which is problematic
        //         for ui-tests, since they expect a `/` (forward slash) as the
        // connector         between `$DIR` and the filename. So, we replace the
        // backslashes after         the directory, and then we will replace
        // with a forward slash.
        dir.push_str("\\\\");
        dir
    };

    #[cfg(not(target_os = "windows"))]
    let test_dir = {
        let mut dir = adjust_canonicalisation(path).display().to_string();
        dir.push('/');
        dir
    };

    test_dir
}

/// This function will strip the provided content string of all ANSI escape
/// codes, and replace all references to the test directory with `$DIR`.
fn strip_contents(contents: &str, test: &TestingInput) -> String {
    // Remove any ANSI escape codes generated from the reporting...
    let stripped = ANSI_REGEX.replace_all(contents, "");

    // Replace the directory by `$DIR`
    let test_dir = test.path.parent().unwrap();
    let stringified_test_dir = stringify_test_dir_path(test_dir);
    let dir_regex = Regex::new(stringified_test_dir.as_str()).unwrap();

    // @@Hack: the forward slash at the end is unconditional, since we
    // need to re-add it because we removed it in the `stringify_test_dir_path`
    // function.
    let stripped = dir_regex.replace_all(stripped.as_ref(), r"$$DIR/").replace("\r\n", "\n");

    stripped
}

/// Given the testing input, and a pre-filtered [Vec<Report>] based on
/// the testing input parameters, render the reports and compare them
/// to the saved corresponding `.stderr` file.
fn compare_emitted_diagnostics(
    input: &TestingInput,
    diagnostics: Vec<Report>,
) -> std::io::Result<()> {
    // First, convert the diagnostics into a string.
    let contents =
        diagnostics.into_iter().map(|report| format!("{}", report)).collect::<Vec<_>>().join("\n");

    compare_output(input, OutputKind::Stderr, contents.as_str())
}

/// This enum is used to specify the kind of output that we are comparing
/// against. This is used to determine which file we are comparing against
/// and also to determine which file we are writing to.
enum OutputKind {
    /// We're comparing the output of the parser to the `.stderr` file
    Stderr,

    /// We're comparing the output of the parser to the `.stdout` file
    Stdout,
}

impl OutputKind {
    /// Get the appropriate extension for the [OutputKind].
    pub fn extension(&self) -> &'static str {
        match self {
            OutputKind::Stderr => "stderr",
            OutputKind::Stdout => "stdout",
        }
    }
}

/// This function will compare the provided contents to the corresponding saved
/// output file, which is either a `.stderr` or `.stdout` file (which is
/// specified by the [OutputKind]). The provided contents are stripped of ANSI
/// escape codes and all directory paths are replaced with `$DIR`.
///
/// If the file does not exist, then it will be created and the contents will be
/// written to it.
///
/// If [`REGENERATE_OUTPUT`] is set to `true`, then the file will be overwritten
/// with the new stripped contents.
fn compare_output(test: &TestingInput, kind: OutputKind, contents: &str) -> std::io::Result<()> {
    let actual_contents = strip_contents(contents, test);

    // We want to load the `.{stderr|stdout}` file and verify that the contents of
    // the file match to the created report. If the `.stderr` file does not
    // exist then we create it and write the generated report to that file
    let test_dir = test.path.parent().unwrap();
    let content_path = test_dir.join(format!("{}.{}", test.filename, kind.extension()));

    // If we specify to re-generate the output, then we will always write the
    // content of the report into the specified file
    if *REGENERATE_OUTPUT || !content_path.exists() {
        // Avoid writing nothing to the `.stderr` case file
        if !actual_contents.is_empty() {
            fs::write(&content_path, &actual_contents)?;
        }
    }

    // We want to delete the file if the contents are empty, and we are
    // re-generating
    if *REGENERATE_OUTPUT && content_path.exists() && actual_contents.is_empty() {
        fs::remove_file(&content_path)?;
    }

    // Read the contents of the file, if we couldn't find the file then we assume
    // that the contents of `.stderr` are empty. We can assume this because the
    // only reason why the file wouldn't be written to is if it didn't exist
    // prior to this and that the contents of the diagnostics are empty, so
    // returning an empty string makes sense here.
    let expected_contents = fs::read_to_string(content_path.clone())
        .unwrap_or_else(|err| match err.kind() {
            io::ErrorKind::NotFound => "".to_string(),
            err => panic!("couldn't open file `{content_path:?}`: {:?}", err),
        })
        .replace("\r\n", "\n");

    pretty_assertions::assert_str_eq!(
        expected_contents,
        actual_contents,
        "\ncase `.{}` does not match for: {:#?}\n",
        kind.extension(),
        test
    );

    Ok(())
}

fn compare_stream(
    test: &TestingInput,
    kind: OutputKind,
    output_stream: &Arc<Mutex<Vec<u8>>>,
) -> io::Result<()> {
    let stream = output_stream.lock().unwrap();
    let contents = std::str::from_utf8(&stream).unwrap();

    compare_output(test, kind, contents)
}

/// This function is used to handle the case of verifying that a parser test was
/// expected to fail. This function verifies that it does fail and that the
/// generated [Report] (which is rendered) matches the recorded `case.stderr`
/// entry within the case.
///
/// If the case specifies that `warnings=ignore`, then warnings will not be
/// considered within the resultant `.stderr` file.
fn handle_failure_case(
    test: TestingInput,
    diagnostics: Vec<Report>,
    output_stream: &Arc<Mutex<Vec<u8>>>,
) -> std::io::Result<()> {
    // verify that the case failed, as in reports where generated
    assert!(
        diagnostics.iter().any(|report| report.is_error()),
        "\ntest case did not fail: {test:#?}{}",
        ""
    );

    // If the test specifies that no warnings should be generated, then check
    // that this is the case
    if test.metadata.warnings == HandleWarnings::Disallow {
        assert!(
            diagnostics.iter().all(|report| report.is_error()),
            "\ntest case generated warnings where they were disallowed: {test:#?}{}",
            ""
        );
    }

    // Filter out `warnings` if the function specifies them to be
    // ignored.
    let diagnostics = diagnostics
        .into_iter()
        .filter(|report| {
            if test.metadata.warnings == HandleWarnings::Ignore { report.is_error() } else { true }
        })
        .collect();

    compare_emitted_diagnostics(&test, diagnostics)?;
    compare_stream(&test, OutputKind::Stdout, output_stream)
}

/// Function that handles a test case which is expected to be successful, in
/// this situation, the function will verify that the test case did not emit any
/// errors or warnings (although setting `warnings=ignore` will ignore
/// warnings).
fn handle_pass_case(
    test: TestingInput,
    diagnostics: Vec<Report>,
    output_stream: &Arc<Mutex<Vec<u8>>>,
) -> std::io::Result<()> {
    let did_pass = match test.metadata.warnings {
        HandleWarnings::Ignore | HandleWarnings::Compare => {
            diagnostics.iter().all(|report| report.is_warning())
        }
        // Expect no diagnostics to be emitted whatsoever
        HandleWarnings::Disallow => diagnostics.is_empty(),
    };

    if !did_pass {
        panic!(
            "\ntest case did not pass:\nconfiguration: {:?}\n\n{}",
            test.metadata,
            diagnostics
                .into_iter()
                .map(|report| format!("{}", report))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    // If we need to compare the output of the warnings, to the previous result...
    if test.metadata.warnings == HandleWarnings::Compare {
        compare_emitted_diagnostics(&test, diagnostics)?;
    }

    compare_stream(&test, OutputKind::Stdout, output_stream)
}

/// The logger that is used by the compiler for `log!` statements.
pub static COMPILER_LOGGER: CompilerLogger = CompilerLogger::new();

/// Generic test handler in the event whether a case should pass or fail.
fn handle_test(test: TestingInput) {
    // we create an error and output stream so that we can later
    // compare the output of the compiler to the expected output
    let raw_output_stream = Arc::new(Mutex::new(Vec::new()));

    let output_stream = || {
        let output_stream = raw_output_stream.clone();
        CompilerOutputStream::Owned(output_stream.clone())
    };
    let error_stream = CompilerOutputStream::stderr;

    COMPILER_LOGGER.error_stream.set(error_stream()).unwrap();
    COMPILER_LOGGER.output_stream.set(output_stream()).unwrap();
    COMPILER_LOGGER.set_messaging_format(CompilerMessagingFormat::Normal);
    log::set_logger(&COMPILER_LOGGER).unwrap_or_else(|_| panic!("couldn't initiate logger"));
    log::set_max_level(log::LevelFilter::Info);

    // We also need to potentially apply any additional configuration options
    // that are specified by the test onto the compiler settings
    let mut settings = if !test.metadata.args.items.is_empty() {
        // @@Hack: push an extra argument to the start of the list to pretend that it
        // is the "program name" that is being executed.
        let mut args = test.metadata.args.items.clone();
        args.insert(0, String::from(""));

        CompilerSettings::parse_from(&args)
    } else {
        CompilerSettings::new()
    };

    // We need at least 2 workers for the parsing loop in order so that the job
    // queue can run within a worker and any other jobs can run inside another
    // worker or workers.
    settings.worker_count = WORKER_COUNT;
    settings.prelude_is_quiet = true;
    settings.set_emit_errors(false);
    settings.set_stage(test.metadata.stage);

    // Specify the entrypoint of the compiler to be the current test path.
    settings.entry_point = Some(test.path.clone());

    // We specify that the output directory should be `tests/target` in order to
    // avoid creating "target" directories within the test runner tree.
    settings.output_directory = Some(Path::new("./target").to_path_buf());

    let interface = Compiler::with(
        settings,
        // @@Future: we might want to directly compare `stderr` rather than
        // rendering diagnostics and then comparing them.
        error_stream,
        {
            let os = raw_output_stream.clone();
            move || CompilerOutputStream::Owned(os.clone())
        },
    )
    .unwrap();

    let mut compiler = CompilerBuilder::build_with_interface(interface);

    // // Now parse the module and store the result
    compiler.run_on_entry_point();
    compiler.maybe_run_executable();

    // @@Copying: we shouldn't really need to clone the diagnostics here!!
    let diagnostics = compiler.diagnostics().to_owned();

    // Based on the specified metadata within the test case itself, we know
    // whether the test should fail or not
    if test.metadata.completion == TestResult::Fail {
        handle_failure_case(test, diagnostics, &raw_output_stream).unwrap();
    } else {
        handle_pass_case(test, diagnostics, &raw_output_stream).unwrap();
    }
}

// Generate all the tests
generate_tests!("./cases/", r"^*\.hash$", "ui", handle_test);
