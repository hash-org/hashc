//! Testing utilities for running various tests that might include
//! resources on the disk. This file primarily has the `generate_tests` macro
//! that will read a directory and generate various test cases from the provided
//! `case.hash` files and names of the directories that contain the cases.
#![feature(iter_intersperse, path_file_prefix, try_find, proc_macro_span)]

use std::{
    fs, io, iter,
    path::{Path, PathBuf},
};

use convert_case::{Case, Casing};
use hash_testing_internal::metadata::{parse_test_case_metadata, TestMetadata};
use proc_macro::{Span, TokenStream};
use quote::{format_ident, quote};
use regex::Regex;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token::Comma,
    Expr,
};

/// Struct representing parameter inputs to the [`generate_tests!`] proc macro.
#[derive(Debug)]
struct GenerateTestsInput {
    /// The entry point of the `ui_tests`
    path: String,
    /// What is the function that handles each test case.
    func: Expr,
    /// What pattern to use when matching for case files.
    test_pattern: String,

    /// prefix to use for when generating each test case.
    test_prefix: String,
}

impl Parse for GenerateTestsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let parse_str_lit = |expr: &Expr| -> syn::Result<String> {
            let str_lit_err = || syn::Error::new_spanned(expr, "Expecting string literal");

            match expr {
                Expr::Lit(expr_lit) => match &expr_lit.lit {
                    syn::Lit::Str(str) => Ok(str.value()),
                    _ => Err(str_lit_err()),
                },
                _ => Err(str_lit_err()),
            }
        };

        let mut result = Punctuated::<Expr, Comma>::parse_terminated(input)?;
        let args_err = || syn::Error::new(input.span(), "Expecting three arguments to macro");

        let func = result.pop().ok_or_else(args_err)?;
        let test_prefix = result.pop().ok_or_else(args_err)?;
        let test_pattern = result.pop().ok_or_else(args_err)?;
        let path = result.pop().ok_or_else(args_err)?;

        if !result.is_empty() {
            return Err(args_err());
        }

        Ok(GenerateTestsInput {
            path: parse_str_lit(path.value())?,
            test_pattern: parse_str_lit(test_pattern.value())?,
            test_prefix: parse_str_lit(test_prefix.value())?,
            func: func.into_value(),
        })
    }
}

/// A detected case entry, which holds the path of the directory
/// that the file is in, and some other metadata about the test
/// case, such as whether the case should pass, or which compiler
/// stage it should run to, etc.
#[derive(Debug, Clone)]
struct TestEntry {
    /// The path of the test
    path: PathBuf,

    /// Name of the file in snake case, only used to create
    /// the name of the unit test.
    snake_name: String,

    /// file metadata that is generated from checking the top of the file
    /// for any test case configuration settings
    metadata: TestMetadata,
}

/// Function to read a directory and extract all of the test cases within
/// the directory recursively. The function will collect all files that match
/// the specified `test_pattern`.
fn read_tests_from_dir(
    path: &Path,
    test_pattern: &Regex,
    base_name: Option<&str>,
) -> io::Result<Vec<TestEntry>> {
    let mut entries = vec![];

    for entry in path.read_dir()? {
        let entry = entry?;
        let path = entry.path();

        let entry_snake_name = path.file_stem().unwrap().to_str().unwrap().to_case(Case::Snake);

        let snake_name: String = base_name
            .into_iter()
            .chain(iter::once(entry_snake_name.as_str()))
            .intersperse("_")
            .collect();

        // Get the metadata for the current path...
        let entry_metadata = entry.metadata()?;

        // If this is a `directory`, then we recurse and perform
        // the same operation, otherwise if it is a file, then
        // we check if name matches the regex pattern and add it
        // to the entries if so...
        if entry_metadata.is_dir() {
            entries.extend(read_tests_from_dir(&path, test_pattern, Some(&snake_name))?);
        } else if entry_metadata.is_file()
            && test_pattern.is_match(path.file_name().unwrap().to_str().unwrap())
        {
            let metadata =
                parse_test_case_metadata(&path).unwrap_or_else(|_| TestMetadata::default());

            entries.push(TestEntry { path, snake_name, metadata });
        }
    }

    Ok(entries)
}

/// Generate test cases based on a directory structure.
///
/// Test cases are generated based on a given test folder path (see `TEST_DIR`
/// below). Each generated test corresponds to the full path of each "wanted"
/// (see `TEST_PATTERN` below) leaf node of the test folder structure, converted
/// to snake case. For example, for a file path `number_tests/is_valid_number.
/// hash`, a test function named `test_number_tests_is_valid_number`
/// will be generated.
///
/// The format of this macro is as follows:
/// ```ignore
/// generate_tests!(TEST_DIR, TEST_PATTERN, TEST_FN);
/// ```
///
/// - `TEST_DIR` must be a string literal path, relative to the file in which
///   the macro is invoked,
/// which is the root directory of the test folder structure (whose name is not
/// included in the test function names).
///
/// - `TEST_PATTERN` must be a string literal regular expression, which should
///   match some leaf node
/// of the test folder structure. The generator will stop generating sub-tests
/// for a subfolder once any file in that subfolder matches `TEST_PATTERN`. For
/// example, if the test folder structure is such that some test folder
/// `test_foo/` contains files `case.hash` and `output`, specifying either of `"
/// output"` or `"case.hash"` as `TEST_PATTERN` will result in a test case being
/// generated for `test_foo`, but no further (i.e. not `test_foo_output` or
/// `test_foo_case_hash`).
///
/// - `FN_PREFIX` is a unique prefix for the generated function in case the
///   macro is used more than once
/// in a single file for generating more than one test file with a potentially
/// different internal test logic. The prefix must be a specified string
/// literal, leaving it empty will generate the normal test name.
///
/// - `TEST_FN` must be an expression of type
///   [`TestingFn`](hash_utils::testing::TestingFn). Every
/// generated test case body will invoke this function with the appropriate
/// [`TestingInput`](hash_utils::testing::TestingInput). Within this function,
/// the actual test logic should be written.
#[proc_macro]
pub fn generate_tests(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as GenerateTestsInput);
    let test_func = input.func;

    let test_path = PathBuf::from(&input.path);
    let call_site = Span::call_site();

    let file_path = fs::canonicalize(
        call_site.source_file().path().parent().unwrap().to_owned().join(test_path),
    )
    .unwrap();

    let test_pattern = Regex::new(&input.test_pattern).unwrap();

    let mut entries = read_tests_from_dir(&file_path, &test_pattern, None).unwrap();
    entries.sort_by_cached_key(|entry| entry.path.to_owned());

    // Compute the test parameters from each entry
    let paths = entries.iter().map(|entry| entry.path.to_str().unwrap());
    let filenames = entries.iter().map(|entry| entry.path.file_prefix().unwrap().to_str().unwrap());
    let case_metadata = entries.iter().map(|entry| entry.metadata);

    // Create the test names from the provided prefix and the computed `snake_name`
    let test_names = entries
        .iter()
        .map(|entry| format_ident!("{}_test_{}", input.test_prefix, entry.snake_name));

    // Create the tests
    let output = quote! {
        #(
            #[test]
            fn #test_names() {
                use hash_testing_internal::metadata::TestMetadata;
                use hash_pipeline::settings::CompilerMode;

                #test_func(TestingInput {
                    path: #paths.into(),
                    filename: #filenames.into(),
                    metadata: #case_metadata.into()
                });
            }
        )*
    };

    output.into()
}
