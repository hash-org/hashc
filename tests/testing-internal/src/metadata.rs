//! Contains a file metadata builder which is able
//! to parse metadata about a unit test based on the
//! first line of input within the test.

use std::{
    fs,
    io::{self, BufRead, BufReader},
    path::PathBuf,
};

use hash_pipeline::settings::CompilerStageKind;
use itertools::{Itertools, peek_nth};
use quote::{ToTokens, quote};

/// Whether the test should pass or fail, and possibly
/// in the future if `warnings` are allowed within the
/// test result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TestResult {
    /// The test case should fail and output errors. If no
    /// errors are emitted by the compiler for the stage, this
    /// means that the test did not fail.
    Fail,
    /// The compiler should not emit any errors or warnings.
    #[default]
    Pass,
}

impl ToTokens for TestResult {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let item: quote::__private::TokenStream = format!("TestResult::{self:?}").parse().unwrap();
        tokens.extend(item)
    }
}

/// This is a wrapper around a [`Vec<String>`] in order to implement the
/// [`ToTokens`] trait, for use with the [`quote!`] macro.
#[derive(Debug, Clone, Default)]
pub struct TestArgs {
    /// The inner vector of items.
    pub items: Vec<String>,
}

impl TestArgs {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn push(&mut self, item: impl Into<String>) {
        self.items.push(item.into())
    }
}

impl FromIterator<String> for TestArgs {
    fn from_iter<I: IntoIterator<Item = String>>(iter: I) -> Self {
        let mut items = Self::new();
        items.items.extend(iter);
        items
    }
}

impl ToTokens for TestArgs {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let items = self.items.iter().map(|item| {
            format!("String::from({item:?})").parse::<quote::__private::TokenStream>().unwrap()
        });

        tokens.extend(quote! { TestArgs { items: vec![#(#items),*] } });
    }
}

/// How the test should handle warnings, whether to ignore, disallow
/// or compare the warning output with the previous output of the
/// UI test.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum HandleWarnings {
    /// Warnings should just be ignored by the test.
    Ignore,
    /// Compare rendered warnings with the ones saved on
    /// disk. This setting is particularly relevant when
    /// the test is expected to pass.
    #[default]
    Compare,

    /// Warnings should be disallowed, this test should
    /// not emit any warnings (provided that it does not)
    /// fail compilation.
    ///
    /// If the test is expected to fail compilation, this
    /// setting is essentially ignored.
    Disallow,
}

impl ToTokens for HandleWarnings {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let item: quote::__private::TokenStream =
            format!("HandleWarnings::{self:?}").parse().unwrap();
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
#[derive(Debug, Clone, Default)]
pub struct TestMetadata {
    /// The compiler stage should the test reach before stopping.
    pub stage: CompilerStageKind,

    /// How should the test complete, pass or fail.
    pub completion: TestResult,

    /// Arguments that have been supplied to the test case. This is used
    /// to pass specific compiler configuration per test case.
    pub args: TestArgs,

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

    /// A flag that specifies if the test should be skipped, if so the
    /// test will be generated, but will be "ignored" when running.
    pub skip: bool,
}

impl ToTokens for TestMetadata {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let TestMetadata { stage, completion, warnings, args, skip } = &self;
        let args = args.clone();

        // Convert the stage into the `tokenised` stage...
        let stage: quote::__private::TokenStream =
            format!("CompilerStageKind::{stage:?}").parse().unwrap();

        tokens.extend(quote! ( TestMetadata {
            completion: #completion,
            stage: #stage,
            warnings: #warnings,
            args: #args,
            skip: #skip
        }))
    }
}

#[derive(Debug, Default)]
pub struct TestMetadataBuilder {
    /// Stage that the test should run to
    stage: Option<CompilerStageKind>,

    /// Whether the test is expected to pass or fail.
    completion: Option<TestResult>,

    /// Arguments that have been supplied to the test case. This is used
    /// to pass specific compiler configuration per test case.
    args: TestArgs,

    /// Whether the test can ignore warnings.
    warnings: Option<HandleWarnings>,

    /// Whether the test should be skipped.
    skip: bool,
}

impl TestMetadataBuilder {
    /// Create a new [TestMetadataBuilder]
    pub fn new() -> Self {
        Self { stage: None, completion: None, warnings: None, skip: false, args: TestArgs::new() }
    }

    /// Add a stage value to the test.
    pub fn with_stage(&mut self, stage: CompilerStageKind) -> &mut Self {
        self.stage = Some(stage);
        self
    }

    /// Add test case arguments to the test.
    pub fn with_args(&mut self, args: TestArgs) -> &mut Self {
        self.args = args;
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

    /// Specify that the test should be skipped when running.
    pub fn with_skip(&mut self, value: bool) -> &mut Self {
        self.skip = value;
        self
    }

    /// Build the [TestMetadata], defaulting to the specified defaults
    /// for any missing property.
    pub fn build(self) -> TestMetadata {
        let TestMetadata { stage, completion, warnings, .. } = TestMetadata::default();

        TestMetadata {
            completion: self.completion.unwrap_or(completion),
            stage: self.stage.unwrap_or(stage),
            warnings: self.warnings.unwrap_or(warnings),
            args: self.args,
            skip: self.skip,
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
    /// Create a new [ParseWarning] for an unrecognised value.
    fn unrecognised_value(key: String, value: String) -> Self {
        Self::UnrecognisedValue { key, value }
    }

    /// Create a new [ParseWarning] for an unrecognised key.
    fn unrecognised_key(key: String) -> Self {
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
/// [CompilerStageKind::Parse].
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

        // Turn the line into chars, start after `//`
        let mut config = peek_nth(source.chars().skip(2));

        // Continue eating `key=value` pairs until we reach the end of the input
        while config.peek().is_some() {
            // if this is a whitespace character, then we skip it
            if matches!(config.peek(), Some(' ')) {
                config.advance_by(1).unwrap();
                continue;
            }

            // Try and parse a key...
            let key = config.take_while_ref(|c| *c != '=').collect::<String>();

            // Parse the `=`
            if matches!(config.peek(), Some('=')) {
                config.advance_by(1).unwrap();
            }

            // Parse the `value` of the key
            let value =
                config.take_while_ref(|c| *c != ',').collect::<String>().trim_end().to_string();

            match key.as_str() {
                "run" => {
                    let value = match value.as_str() {
                        "fail" => TestResult::Fail,
                        "pass" => TestResult::Pass,
                        // We always default `pass` here
                        _ => {
                            warnings.push(ParseWarning::unrecognised_value(key, value));
                            TestResult::Pass
                        }
                    };

                    builder.with_completion(value);
                }
                "stage" => {
                    let stage = match value.as_str() {
                        "parse" => CompilerStageKind::Parse,
                        "semantic" => CompilerStageKind::UntypedAnalysis,
                        "typecheck" => CompilerStageKind::Analysis,
                        "ir" => CompilerStageKind::Lower,
                        "codegen" => CompilerStageKind::CodeGen,
                        "full" => CompilerStageKind::Build,
                        "exe" => CompilerStageKind::Exe,
                        // We always default to `full` here
                        _ => {
                            warnings.push(ParseWarning::unrecognised_value(key, value));
                            CompilerStageKind::Build
                        }
                    };

                    builder.with_stage(stage);
                }
                "args" => {
                    // @@Todo: we should support a simple string syntax here in order
                    // to allow for the user to provide the arguments as a string, since
                    // currently the special character like `,` will break the parsing.
                    let args = value.split(' ').map(|s| s.to_string()).collect();
                    builder.with_args(args);
                }
                "warnings" => {
                    let action = match value.as_str() {
                        "ignore" => HandleWarnings::Ignore,
                        "disallow" => HandleWarnings::Disallow,
                        "compare" => HandleWarnings::Compare,
                        _ => {
                            warnings.push(ParseWarning::unrecognised_value(key, value));
                            HandleWarnings::Compare
                        }
                    };
                    builder.with_ignore_warnings(action);
                }
                "skip" => {
                    let skip = match value.as_str() {
                        "true" => true,
                        "false" => false,
                        _ => {
                            warnings.push(ParseWarning::unrecognised_value(key, value));
                            false
                        }
                    };

                    builder.with_skip(skip);
                }
                _ => {
                    warnings.push(ParseWarning::unrecognised_key(key));
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
