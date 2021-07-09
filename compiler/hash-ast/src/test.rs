use hash_utils::testing::TestingInput;

fn _handle_test(_input: TestingInput) {
    // @@Todo: write testing logic for parsing
    assert_ne!(1, 2);
}

mod tests {
    use hash_utils_testing_macros::generate_tests;

    // "case.hash" is the test pattern.
    generate_tests!("../test/", r"^case\.hash$", _handle_test);
}
