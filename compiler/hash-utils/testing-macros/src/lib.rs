#![feature(proc_macro_span)]
#![feature(iter_intersperse)]
#![feature(try_find)]

use convert_case::{Case, Casing};
use proc_macro::{Span, TokenStream};
use quote::{format_ident, quote};
use regex::Regex;
use std::{
    fs, io, iter,
    path::{Path, PathBuf},
};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token::Comma,
    Expr,
};

#[derive(Debug)]
struct GenerateTestsInput {
    path: String,
    func: Expr,
    test_pattern: String,
}

fn parse_str_lit(expr: &Expr) -> syn::Result<String> {
    let str_lit_err = || syn::Error::new_spanned(expr, "Expecting string literal");

    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Str(str) => Ok(str.value()),
            _ => Err(str_lit_err()),
        },
        _ => Err(str_lit_err()),
    }
}

impl Parse for GenerateTestsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut result = Punctuated::<Expr, Comma>::parse_terminated(input)?;
        let args_err = || syn::Error::new(input.span(), "Expecting two arguments to macro");

        let func = result.pop().ok_or_else(args_err)?;
        let test_pattern = result.pop().ok_or_else(args_err)?;
        let path = result.pop().ok_or_else(args_err)?;

        if !result.is_empty() {
            return Err(args_err());
        }

        Ok(GenerateTestsInput {
            path: parse_str_lit(path.value())?,
            test_pattern: parse_str_lit(test_pattern.value())?,
            func: func.into_value(),
        })
    }
}

#[derive(Debug, Clone)]
struct FileEntry {
    path: PathBuf,
    snake_name: String,
}

fn read_dir(
    path: &Path,
    test_pattern: &Regex,
    base_name: Option<&str>,
) -> io::Result<Vec<FileEntry>> {
    let mut entries = vec![];

    for entry in path.read_dir()? {
        let entry = entry?;
        let path = entry.path();

        let entry_snake_name = path
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .to_case(Case::Snake);
        let snake_name: String = base_name
            .into_iter()
            .chain(iter::once(entry_snake_name.as_str()))
            .intersperse("_")
            .collect();

        if entry.metadata()?.is_dir() {
            let dir_contents = entry.path().read_dir()?;

            let mut test_found = false;
            for sub_entry in dir_contents {
                if test_pattern.is_match(sub_entry?.file_name().to_str().unwrap()) {
                    test_found = true;
                    break;
                }
            }

            if !test_found {
                entries.extend(read_dir(&path, test_pattern, Some(&snake_name))?);
                continue;
            }
        }

        entries.push(FileEntry { path, snake_name });
    }

    Ok(entries)
}

/// Generate test cases based on a directory structure.
///
/// Test cases are generated based on a given test folder path (see `TEST_DIR` below). Each
/// generated test corresponds to the full path of each "wanted" (see `TEST_PATTERN` below) leaf
/// node of the test folder structure, converted to snake case. For example, for a file path
/// `number_tests/is_valid_number.hash`, a test function named `test_number_tests_is_valid_number`
/// will be generated.
///
/// The format of this macro is as follows:
/// ```notrust
/// generate_tests!(TEST_DIR, TEST_PATTERN, TEST_FN);
/// ```
///
/// - `TEST_DIR` must be a string literal path, relative to the file in which the macro is invoked,
/// which is the root directory of the test folder structure (whose name is not included in the
/// test function names).
///
/// - `TEST_PATTERN` must be a string literal regular expression, which should match some leaf node
/// of the test folder structure. The generator will stop generating sub-tests for a subfolder once
/// any file in that subfolder matches `TEST_PATTERN`. For example, if the test folder structure is
/// such that some test folder `test_foo/` contains files `case.hash` and `output`, specifying
/// either of `"output"` or `"case.hash"` as `TEST_PATTERN` will result in a test case being
/// generated for `test_foo`, but no further (i.e. not `test_foo_output` or `test_foo_case_hash`).
///
/// - `TEST_FN` must be an expression of type [`TestingFn`](hash_utils::testing::TestingFn). Every
/// generated test case body will invoke this function with the appropriate
/// [`TestingInput`](hash_utils::testing::TestingInput). Within this function, the actual test
/// logic should be written.
#[proc_macro]
pub fn generate_tests(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as GenerateTestsInput);
    let test_func = input.func;

    let test_path = PathBuf::from(&input.path);
    let call_site = Span::call_site();

    let file_path = fs::canonicalize(
        call_site
            .source_file()
            .path()
            .parent()
            .unwrap()
            .to_owned()
            .join(test_path),
    )
    .unwrap();

    let test_pattern = Regex::new(&input.test_pattern).unwrap();
    let entries = read_dir(&file_path, &test_pattern, None).unwrap();

    let paths = entries.iter().map(|entry| entry.path.to_str().unwrap());
    let snake_names = entries.iter().map(|entry| entry.snake_name.to_owned());
    let test_names = entries
        .iter()
        .map(|entry| format_ident!("test_{}", entry.snake_name));

    let output = quote! {
        #(
            #[test]
            fn #test_names() {
                #test_func(TestingInput { path: #paths.into(), snake_name: #snake_names.into() });
            }
        )*
    };

    output.into()
}
