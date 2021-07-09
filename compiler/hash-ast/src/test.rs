use std::fs;

use hash_utils::testing::TestingInput;

fn handle_test(input: TestingInput) {
    // @@Todo: write testing logic for parsing
    assert_eq!("a", "a");
}

mod tests {
    use super::*;
    use hash_utils_testing_macros::generate_tests;

    // "case.hash" is the test pattern.
    generate_tests!("../test/", r"^case\.hash$", handle_test);
}
