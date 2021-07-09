use std::path::PathBuf;

// pub struct TestingSuccess {
//     visualiser_output: String,
//     ast_debug_output: String,
// }

// pub struct TestingFailure {
//     error_debug_output: String,
// }

// pub type TestingResult = Result<TestingSuccess, TestingFailure>;

#[derive(Debug, Clone)]
pub struct TestingInput {
    pub path: PathBuf,
    pub snake_name: String,
}

pub type TestingFn = fn(input: TestingInput);
