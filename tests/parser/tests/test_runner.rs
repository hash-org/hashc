#![cfg(test)]

use std::num::NonZeroUsize;

use hash_alloc::Castle;
use hash_ast::parse::{ParParser, Parser, ParserBackend};
use hash_parser::backend::HashParser;
use hash_pest_parser::backend::HashPestParser;
use hash_utils::testing::TestingInput;
use hash_utils_testing_macros::generate_tests;

// fn handle_success_case() {}

// fn handle_failure_case() {}

fn handle_test<'a>(input: TestingInput, parser: impl ParserBackend<'a>) {
    // determine if this test should fail or not
    let should_fail = input.snake_name.starts_with("should_fail");

    let content_path = input.path.join("case.hash");

    let parser = ParParser::new_with_workers(parser, NonZeroUsize::new(1).unwrap(), false);

    // Now parse the module and store the result
    let result = parser.parse(&content_path, input.path);

    // Check whether the result fails or not, depending on if the file_path begins with
    // 'should_fail'...
    assert_eq!(result.0.is_err(), should_fail);
}

fn run_hash_parser_tests(input: TestingInput) {
    let castle = Castle::new();
    let hash_parser = HashParser::new(&castle);

    handle_test(input, hash_parser)
}

fn run_pest_parser_tests(input: TestingInput) {
    let castle = Castle::new();
    let pest_parser = HashPestParser::new(&castle);

    handle_test(input, pest_parser)
}

// "case.hash" is the test pattern.
generate_tests!("./cases/", r"^case\.hash$", "self", run_hash_parser_tests);
generate_tests!("./cases/", r"^case\.hash$", "pest", run_pest_parser_tests);
