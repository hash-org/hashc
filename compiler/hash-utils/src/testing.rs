pub struct TestingSuccess {
    visualiser_output: String,
    ast_debug_output: String,
}

pub struct TestingFailure {
    error_debug_output: String,
}

pub struct TestingInput {
    filename: String,
    directory: String,
}

pub type TestingResult = Result<TestingSuccess, TestingFailure>;
