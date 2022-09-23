//! Contains a file metadata builder which is able
//! to parse metadata about a unit test based on the
//! first line of input within the test.

use std::{
    fs,
    io::{self, BufRead, BufReader},
    path::PathBuf,
};

use hash_pipeline::settings::CompilerMode;
use itertools::{peek_nth, Itertools};
use quote::{quote, ToTokens};

/// Whether the test should pass or fail, and possibly
/// in the future if `warnings` are allowed within the
/// test result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestResult {
    /// The test case should fail and output errors. If no
    /// errors are emitted by the compiler for the stage, this
    /// means that the test did not fail.
    Fail,
    /// The compiler should not emit any errors or warnings.
    Pass,
}

impl Default for TestResult {
    fn default() -> Self {
        TestResult::Pass
    }
}

impl ToTokens for TestResult {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let item: quote::__private::TokenStream =
            format!("TestResult::{:?}", self).parse().unwrap();
        tokens.extend(item)
    }
}

/// How the test should handle warnings, whether to ignore, disallow
/// or compare the warning output with the previous output of the
/// UI test.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandleWarnings {
    /// Warnings should just be ignored by the test.
    Ignore,
    /// Compare rendered warnings with the ones saved on
    /// disk. This setting is particularly relevant when
    /// the test is expected to pass.
    Compare,

    /// Warnings should be disallowed, this test should
    /// not emit any warnings (provided that it does not)
    /// fail compilation.
    ///
    /// If the test is expected to fail compilation, this
    /// setting is essentially ignored.
    Disallow,
}

impl Default for HandleWarnings {
    fn default() -> Self {
        HandleWarnings::Compare
    }
}

impl ToTokens for HandleWarnings {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let item: quote::__private::TokenStream =
            format!("HandleWarnings::{:?}", self).parse().unwrap();
        tokens.extend(item)
    }
}

/// Metadata about a specific test case, derived from the
/// comment at the top of the file if any... if no comment
/// is found, or parsing the comment fails, then the
/// default [TestMetadata] is assumed which means two things:
///
/// - The test should succeed
///
/// - The test runs the entire pipeline
#[derive(Debug, Clone, Copy, Default)]
pub struct TestMetadata {
    /// The compiler stage should the test reach before stopping.
    pub stage: CompilerMode,
    /// How should the test complete, pass or fail.
    pub completion: TestResult,
    /// If the test should ignore any emitted warnings.
    ///
    /// - If this setting is specified, and when the `completion` is set to
    ///   [TestResult::Pass], the function will see if any of the reports are
    ///   errors, and then  base this if the compilation failed.
    ///
    /// - If this settings is specified, abd when the `completion` is set to
    ///   [TestResult::Fail], the handler will ignore any generated `warning`
    ///   reports when comparing the output of the erroneous case. However, a
    ///   test case that produces no errors, but warnings will still fail since
    ///   it did not `fail` compilation.
    pub warnings: HandleWarnings,
}

impl ToTokens for TestMetadata {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let TestMetadata { stage, completion, warnings } = *self;

        // Convert the stage into the `tokenised` stage...
        let stage: quote::__private::TokenStream =
            format!("CompilerMode::{:?}", stage).parse().unwrap();

        tokens.extend(
            quote! ( TestMetadata { completion: #completion, stage: #stage, warnings: #warnings  }),
        )
    }
}

#[derive(Debug, Default)]
pub struct TestMetadataBuilder {
    /// Stage that the test should run to
    stage: Option<CompilerMode>,

    /// Whether the test is expected to pass or fail.
    completion: Option<TestResult>,

    /// Whether the test can ignore warnings.
    warnings: Option<HandleWarnings>,
}

impl TestMetadataBuilder {
    /// Create a new [TestMetadataBuilder]
    pub fn new() -> Self {
        Self { stage: None, completion: None, warnings: None }
    }

    /// Add a stage value to the test.
    pub fn with_stage(&mut self, stage: CompilerMode) -> &mut Self {
        self.stage = Some(stage);
        self
    }

    /// Add a `completion` value to the test.
    pub fn with_completion(&mut self, completion: TestResult) -> &mut Self {
        self.completion = Some(completion);
        self
    }

    /// Specify whether the test should ignore warnings
    pub fn with_ignore_warnings(&mut self, value: HandleWarnings) -> &mut Self {
        self.warnings = Some(value);
        self
    }

    /// Build the [TestMetadata], defaulting to the specified defaults
    /// for any missing property.
    pub fn build(&mut self) -> TestMetadata {
        let TestMetadata { stage, completion, warnings } = TestMetadata::default();

        TestMetadata {
            completion: self.completion.unwrap_or(completion),
            stage: self.stage.unwrap_or(stage),
            warnings: self.warnings.unwrap_or(warnings),
        }
    }
}

/// A [ParseWarning] is emitted by the metadata parsing function, which detects
/// invalid configurations within test cases. When the result from
/// [ParsedMetadata] is used, these warnings are later emitted using the
/// `proc_macro` diagnostic emission API.
pub enum ParseWarning {
    /// An unrecognised value for a key was provided.
    UnrecognisedValue { key: String, value: String },
    /// Some specified `key` was not recognised for the configuration
    UnrecognisedKey { key: String },
}

impl ParseWarning {
    fn new_unrecognised_value(key: String, value: String) -> Self {
        Self::UnrecognisedValue { key, value }
    }

    fn new_unrecognised_key(key: String) -> Self {
        Self::UnrecognisedKey { key }
    }
}

pub struct ParsedMetadata {
    pub metadata: TestMetadata,
    /// Any warning that is generated about the parsed metadata from
    /// the test case.
    pub warnings: Vec<ParseWarning>,
}

/// Function to parse the [TestMetadata] from the test file specified by the
/// path. The function will attempt to read the file at the provided
/// path, read the first line and attempt to parse test configuration
/// settings from the line which are comma separated key value pairs
/// like so:
///
/// ```ignore
/// // run=pass,stage=parse
/// main := () => {
///     print("parse test");
/// };
/// ```
/// From the above example, this function will produce a [TestMetadata] that
/// specifies that this test should `pass` and should only run up until the
/// [CompilerMode::Parse].
pub fn parse_test_case_metadata(path: &PathBuf) -> Result<ParsedMetadata, io::Error> {
    let mut source = String::new();

    // Read the first line of the file into `title`.
    let file = fs::File::open(path)?;
    let mut buffer = BufReader::new(file);
    let _ = buffer.read_line(&mut source)?;

    // We need to strip the shebang line, if it starts with `#!` then
    // it should skip the current line and read the next line
    if source.starts_with("#!") {
        source.clear();
        let _ = buffer.read_line(&mut source)?;
    }

    let mut warnings = vec![];

    // Now we begin the parsing of the line...
    if source.starts_with("//") {
        let mut builder = TestMetadataBuilder::new();

        // Turn the line into chars, strip all white-spaces and start after `//`
        let mut config = peek_nth(source.chars().filter(|c| !c.is_whitespace()).skip(2));

        // Continue eating `key=value` pairs until we reach the end of the input
        while config.peek().is_some() {
            // Try and parse a key...
            let key = config.take_while_ref(|c| *c != '=').collect::<String>();

            // Parse the `=`
            if matches!(config.peek(), Some('=')) {
                config.advance_by(1).unwrap();
            }

            // Parse the `value` of the key
            let value = config.take_while_ref(|c| *c != ',').collect::<String>();

            match key.as_str() {
                "run" => {
                    let value = match value.as_str() {
                        "fail" => TestResult::Fail,
                        "pass" => TestResult::Pass,
                        // We always default `pass` here
                        _ => {
                            warnings.push(ParseWarning::new_unrecognised_value(key, value));
                            TestResult::Pass
                        }
                    };

                    builder.with_completion(value);
                }
                "stage" => {
                    let stage = match value.as_str() {
                        "parse" => CompilerMode::Parse,
                        "semantic" => CompilerMode::SemanticPass,
                        "typecheck" => CompilerMode::Typecheck,
                        "ir" => CompilerMode::IrGen,
                        "full" => CompilerMode::Full,
                        // We always default to `full` here
                        _ => {
                            warnings.push(ParseWarning::new_unrecognised_value(key, value));
                            CompilerMode::Full
                        }
                    };

                    builder.with_stage(stage);
                }
                "warnings" => {
                    let action = match value.as_str() {
                        "ignore" => HandleWarnings::Ignore,
                        "disallow" => HandleWarnings::Disallow,
                        "compare" => HandleWarnings::Compare,
                        _ => {
                            warnings.push(ParseWarning::new_unrecognised_value(key, value));
                            HandleWarnings::Compare
                        }
                    };
                    builder.with_ignore_warnings(action);
                }
                _ => {
                    warnings.push(ParseWarning::new_unrecognised_key(key));
                    break;
                }
            }

            // Parse an optional comma `,`
            if config.peek_nth(2).is_some() && matches!(config.peek(), Some(',')) {
                config.advance_by(1).unwrap();
            }
        }

        Ok(ParsedMetadata { warnings, metadata: builder.build() })
    } else {
        Ok(ParsedMetadata { warnings, metadata: TestMetadata::default() })
    }
}
