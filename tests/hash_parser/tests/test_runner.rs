#![cfg(test)]

use std::num::NonZeroUsize;

use hash_alloc::Castle;
use hash_ast::parse::{ParParser, Parser};
use hash_parser::backend::HashParser;
use hash_utils::testing::TestingInput;
use hash_utils_testing_macros::generate_tests;

fn handle_test(input: TestingInput) {
    // determine if this test should fail or not
    let should_fail = input.snake_name.starts_with("should_fail");


    let content_path = input.path.join("case.hash");

    let castle = Castle::new();
    let parser = ParParser::new_with_workers(HashParser::new(&castle), NonZeroUsize::new(1).unwrap(), false);

    // Now parse the module and store the result
    let result =  parser.parse(&content_path, input.path);

    // Check whether the result fails or not, depending on if the file_path begins with 
    // 'should_fail'...
    assert_eq!(result.0.is_err(), should_fail);
}

// "case.hash" is the test pattern.
generate_tests!("./cases/", r"^case\.hash$", handle_test);
