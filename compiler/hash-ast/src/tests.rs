#![cfg(test)]

use hash_utils::testing::TestingInput;
use hash_utils_testing_macros::generate_tests;

fn handle_test(_input: TestingInput) {
    // @@Todo: write testing logic for parsing
    assert_ne!(1, 2);
}

// "case.hash" is the test pattern.
generate_tests!("../test/", r"^case\.hash$", handle_test);
