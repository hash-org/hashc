#![cfg(test)]

use hash_alloc::Castle;
use hash_parser::parser::HashParser;
use hash_pipeline::{
    sources::{Module, Sources},
    Parser,
};
use hash_source::SourceId;
use hash_utils::testing::TestingInput;
use hash_utils_testing_macros::generate_tests;

// fn handle_success_case() {}

// fn handle_failure_case() {}

fn handle_test(input: TestingInput) {
    // determine if this test should fail or not
    let should_fail = input.snake_name.starts_with("should_fail");
    let castle = Castle::new();

    let mut sources = Sources::new();
    let content_path = input.path.join("case.hash");
    let target = Module::new(content_path.clone());
    let target_id = sources.add_module(target);

    let mut parser = HashParser::new(1, &castle);

    // Now parse the module and store the result
    let result = parser.parse(SourceId::Module(target_id), &mut sources);

    // Check whether the result fails or not, depending on if the file_path begins with
    // 'should_fail'...
    assert_eq!(
        result.is_err(),
        should_fail,
        "parsing file failed: {:?}",
        content_path
    );
}
// "case.hash" is the test pattern.
generate_tests!("./cases/", r"^case\.hash$", "self", handle_test);
